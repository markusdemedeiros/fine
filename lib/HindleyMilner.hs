{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use record patterns" #-}
module HindleyMilner where

import BasicChecker (BasicType (..), FnName, Kind (..), Program, Refinement (..), Term (..), Type (..), Variable, base, bodies, decls, prim)
import Control.Lens (Bifunctor (bimap), over, (%~), (^.))
import Control.Monad
import qualified Control.Monad.State as ST
import Data.Functor ((<&>))
import Data.List (nub)
import Data.Maybe (catMaybes, mapMaybe)
import GHC.Generics (UInt)
import Surface (tyv)
import Util

-- Type checking strategy: (remember-- we ignore all refinements until we insert holes @ call sites!)
--    - Collect the arity of each function iunto a table. This includes function bodies with no type given.
--    - All function arguments will be implicitly given a type (fn)-ty-n
--    - All functions results will be given a type (fn)-ty-r
--    - Now we need to go through each body in the program
--    - 1. We must unify the function arguments against the signautre (w/ arity)
--    - 2. Now going into the body we apply rules at each point using regular unificiation, not rewriting yet.
--        ...
--        When we encounter variable whose name is in the table, read the type as (fn)-ty-0 -> ... -> n-1 -> r. Add appropriate constraints.
--        When
--    - 3. Unify to get an assignment.
--    - 4. Translate the function sigs. Add explicit forall's to the free type variables.
--    - 5. Translate the body.

-- We need a way to generate fresh unification variables.
-- After we're done, we'll need a way to look up each of fn-ty-x. Maybe we use uptrees?
-- Need equations between (trees of) BasicTypes (int, bool, user defined variable), and unification variables (fresh and fn-ty-x)

data UnifVar
  = UnifAtom BasicType
  | Anon Int
  | FnArg FnName Int
  | FnVal FnName
  deriving (Show, Eq)

data UnifType
  = UnifVar UnifVar
  | UnifFn UnifType UnifType
  deriving (Show, Eq)

-- Equality constraints between unification types.
-- The convention is that the type on the left is preferred to the type on the right.
type UnifConstraint = (UnifType, UnifType)

-- Number of arguments for all interp. and uninterp. functions.
-- This serves as a lower bounds on function arities, and (inclues return type. )
-- If the function is in the domain of the Arity table, it has a declared signaure. Otherwise,
--    it either has a binding, or is free (cool!)
-- For functions with a declared type, we get the arity from the number of right branches.
-- For functions with no declared type, their arity is at least 1. Unification will find the precise number.
type Arity = Table FnName Int

-- Global State for creating fresh variables across the program
type ConstraintST = ST.State Int

genty :: ConstraintST String
genty = do
  r <- ST.get
  ST.put (r + 1)
  return $ "tau." ++ show r

gensym :: ConstraintST UnifVar
gensym = do
  r <- ST.get
  ST.put (r + 1)
  return $ Anon r

collectArity :: Program -> Arity
collectArity p = def %~ const (Just 1) $ typeArity <$> p ^. decls
  where
    typeArity :: Type -> Int
    typeArity (TRBase {}) = 1
    typeArity (TDepFn _ _ t) = 1 + typeArity t
    typeArity (TForall {}) = error "illegal type quantifier in typeArity"

-- Get the type associated to a named function
declType :: Arity -> FnName -> UnifType
declType arity name = mkty 0 (getTbl arity name)
  where
    mkty :: Int -> Int -> UnifType
    mkty a n
      | a + 1 == n = UnifVar $ FnVal name
      | a + 1 < n = UnifFn (UnifVar (FnArg name a)) $ mkty (a + 1) n

-- Convert a type into its base form
eraseRefinements :: Type -> UnifType
eraseRefinements (TRBase b _) = UnifVar $ UnifAtom b
eraseRefinements (TDepFn _ t1 t2) = UnifFn (eraseRefinements t1) (eraseRefinements t2)
eraseRefinements (TForall {}) = error "illegal type quantifier in erase refinements"

type Gamma = Table Variable UnifType

-- Get constraints for a single body
-- Synthesize the entire most general type, and constrain it to be equal to (declType)
-- When fresh variables are generated, we also rewrite the program with explicit annotations.
synTerm :: Arity -> FnName -> Term -> ConstraintST ([UnifConstraint], Term)
synTerm a name term = do
  (tau, cs, trm1) <- j (emptyTable Nothing) term
  return $ ((declType a name, tau) : cs, trm1)
  where
    -- Extends Algorithm J
    -- Does not implement let-polymorphism
    -- https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
    j :: Gamma -> Term -> ConstraintST (UnifType, [UnifConstraint], Term)

    -- Constants: Match base type of primitve type
    j g x@(TConst k) = return (eraseRefinements $ prim k, [], x)
    -- Variables:
    --    If v is free, return the declType.
    --    If v is bound, lookup the type in the context.
    --    No new constraints in either case.
    j g x@(TVar v)
      | bContains v (g ^. dom) = return (getTbl g v, [], x)
      | otherwise = error $ "unsupported global function " ++ v -- return (declType a v, [], x)
      -- Let bindings:
      --  For now, we're going to do this the same as lambda. No let-polymorphism.
    j g (TLet x bound body) = do
      (te, ce, bound') <- j g bound
      (tb, cb, body') <- j (tblSet x te g) body
      return (tb, ce ++ cb, TLet x bound' body')
    -- Lambda bindings:
    --  Allocate fresh unification variable tau
    --  Set x to tau in g, check the body to get tau'
    --  Result is tau->tau'; no new bindings.
    j g (TLam x body) = do
      tau <- gensym <&> UnifVar
      (tau', cs, body') <- j (tblSet x tau g) body
      return (UnifFn tau tau', cs, TLam x body')
    -- Annotations:
    --  Get the type of the inner term
    --  Constrain that type to the annotation
    --  Return the preferred type (the annotation)
    j g (TAnn t typ) = do
      (tau, cs, a') <- j g t
      return (eraseRefinements typ, (eraseRefinements typ, tau) : cs, TAnn a' typ)
    j g (TApp e varg) = do
      (tauFunction, cf, e') <- j g e
      (tauArg, cv, eVarg) <- j g (TVar varg)
      -- If the variable is not just a variable (ie. we're applying to a global variable) let-bind to put in ANF
      eNew <- case eVarg of
        (TVar v') -> return $ TApp e' v'
        ex -> do
          tb <- genty
          return $ TLet tb ex $ TApp e' tb
      tauResult <- gensym <&> UnifVar
      return (tauResult, (UnifFn tauArg tauResult, tauFunction) : cf, TApp e' varg)

    -- Conditionals:
    --  Get the types of all three subterms
    --  Constrain the predicate type to be a boolean
    --  Contrain the tt and tf types to be equal (prefer tt)
    j g (TCond vc tt tf) = do
      -- It is sound to treat vc as if it was a variable term here.
      (tauc, cc, _) <- j g (TVar vc)
      (taut, ct, tt') <- j g tt
      (tauf, cf, tf') <- j g tf
      let condPred = (tauc, UnifVar . UnifAtom $ BBool)
      let branchPred = (taut, tauf)
      return (taut, condPred : branchPred : (cc ++ ct ++ cf), TCond vc tt' tf')

    -- Letrec:
    --  TODO
    j g (TRec v bound ty body) = error "letrec unimplemented in algorithm j"
    j _ _ = error "unhandled case in algorithm j"

-- Get constraints for a single function declaration
synDecl :: Arity -> FnName -> Type -> [UnifConstraint]
synDecl a name typ = [(eraseRefinements typ, declType a name)]

-- Get all of the type inference constraints for a program
constrain :: Program -> ([UnifConstraint], Program)
constrain p = (declConstraints ++ bodyConstraints, finalProgram)
  where
    arity = collectArity p
    declConstraints = concatMap (\nm -> synDecl arity nm (getTbl (p ^. decls) nm)) (p ^. decls . dom)
    bodyConstraints = fst bodyResults
    finalProgram = bodies %~ const (snd bodyResults) $ p

    bodyResults = fst . flip ST.runState 0 $ foldM (\(csf, psf) nm -> synTerm arity nm (getTbl (p ^. bodies) nm) >>= (\(x, y) -> return (x ++ csf, tblSet nm y psf))) ([], p ^. bodies) (p ^. bodies . dom)

-- Helpful for debugging
showConstraints :: Program -> IO ()
showConstraints p = mapM_ (putStrLn . pretty) (fst (constrain p))
  where
    pretty :: UnifConstraint -> String
    pretty (c0, c1) = pretty' c0 ++ " = " ++ pretty' c1 ++ ";"
    pretty' (UnifVar uv) = pretty'' uv
    pretty' (UnifFn (UnifVar uv) tr) = pretty'' uv ++ " -> " ++ pretty' tr
    pretty' (UnifFn ta tr) = pretty' ta ++ " -> " ++ pretty' tr

    pretty'' (UnifAtom b) = show b
    pretty'' (Anon i) = "tmp." ++ show i
    pretty'' (FnArg name i) = name ++ ".arg." ++ show i
    pretty'' (FnVal name) = name ++ ".val"

-- Indeterminate types, must be mapped from.
data UVar
  = UAnon Int
  | UFnAg FnName Int
  | UFnR FnName
  | UserVar String
  deriving (Show, Eq)

-- Grounded types.
data UConcrete
  = UBool
  | UInt
  deriving (Show, Eq)

-- Trees of types.
data UTy
  = UConc UConcrete
  | UVar UVar
  | UFn UTy UTy
  deriving (Show, Eq)

-- Turn the system of generated constraints into one which treats variables uniformly
-- This could probably be inlined into constraint generation lol
preprocessVariables :: [UnifConstraint] -> [(UTy, UTy)]
preprocessVariables = fmap (bimap p' p')

-- Helper function: Turns a UnifType constraint into a form that treats variables uniformly.
p' :: UnifType -> UTy
p' (UnifFn a b) = UFn (p' a) (p' b)
p' (UnifVar (UnifAtom BInt)) = UConc UInt
p' (UnifVar (UnifAtom BBool)) = UConc UBool
p' (UnifVar (UnifAtom (BTVar v))) = UVar (UserVar v)
p' (UnifVar (Anon i)) = UVar (UAnon i)
p' (UnifVar (FnArg f i)) = UVar (UFnAg f i)
p' (UnifVar (FnVal f)) = UVar (UFnR f)

-- Map from all possible unknowns in the program
type Subst = Table UVar SubstR

-- Result of a substitution.
--    Self: This variable should substitute to itself, in some form.
--    Link v: This variable should substitute to whatever v points to in the table
--    Type: This variable should substitute to the subst of a concrete type
--            eg. if a lookup is Type (a -> Int) then the result is ((lookup a) -> Int)
--    Thus, the uinification of a variable to a variable can say (v0 -> (TermVaraible v1))
--    And the substituter will ensure (TermVariable v1) gets replaced if necessary.
data SubstR
  = Self
  | Type UTy
  deriving (Eq, Show)

unify :: [(UTy, UTy)] -> Subst
unify = unify' (emptyTable $ Just Self)
  where
    unify' tb [] = tb
    unify' tb (c : cs) = unify' (unify1 tb c) cs

    unify1 :: Subst -> (UTy, UTy) -> Subst
    -- Constants unify when they are equal
    unify1 tb (UConc c1, UConc c2)
      | c1 == c1 = tb
      | otherwise = error "unify failed; inconsistent concrete types"
    -- Functions unify to other functions if their subterms do
    unify1 tb (UFn a1 b1, UFn a2 b2) = unify1 (unify1 tb (a1, a2)) (b1, b2)
    -- Variables unify when we can set one to be the other.
    unify1 tb (UVar v1, k) = unifyVarTyp v1 k tb
    unify1 tb (k, UVar v2) = unifyVarTyp v2 k tb
    unify1 tb (x, y) = error $ "cannot unify!\n x=" ++ show x ++ "\n y=" ++ show y ++ " \n tbl=" ++ show tb

    -- Update subst by setting a variable to a type.
    --  2. Switch based on the case of that variable?
    unifyVarTyp :: UVar -> UTy -> Subst -> Subst
    unifyVarTyp v ty tbl =
      --  1. Look up the variable in the subst.
      case findRoot v tbl of
        -- If that variable still leads to an unground variable, set that variable to ty
        (Left rootVar) -> tblSet rootVar (Type ty) tbl
        -- If that variable leads to a constant, unify with that constant.
        (Right (UConc c2)) -> unify1 tbl (UConc c2, ty)
        -- If that variable leads to a function, unify with that function.
        (Right (UFn a2 b2)) -> unify1 tbl (UFn a2 b2, ty)
        -- It is not possible for findRoot to return a UVar
        (Right (UVar v2)) -> error "unreachable"

-- Find the root of a variable in the subst mapping
findRoot :: UVar -> Subst -> Either UVar UTy
findRoot v tb =
  case getTbl tb v of
    Self -> Left v
    -- Do I need to look through variables here?
    (Type (UVar vn)) -> findRoot vn tb
    (Type ut) -> Right ut

subTyp :: Subst -> Type -> Type
subTyp s (TRBase (BTVar v) r) =
  case findRoot (UserVar v) s of
    -- Free type variable; refined to a hole?
    (Left uv) -> uvToTy uv
    (Right ut) -> utyToTy ut
subTyp s (TDepFn v t0 t1) = TDepFn v (subTyp s t0) (subTyp s t1)
subTyp s x = x

uvToTy (UserVar vr) = TRBase (BTVar vr) Hole
uvToTy (UAnon i) = TRBase (BTVar $ "tmp." ++ show i) Hole
uvToTy (UFnAg fn i) = TRBase (BTVar $ fn ++ ".arg." ++ show i) Hole
uvToTy (UFnR fn) = TRBase (BTVar $ fn ++ ".val") Hole

utyToTy = fst . flip utyToTy' 0
  where
    utyToTy' (UConc UBool) i = (TRBase BBool Hole, i)
    utyToTy' (UConc UInt) i = (TRBase BInt Hole, i)
    utyToTy' (UVar uv) i = (uvToTy uv, i)
    utyToTy' (UFn u0 u1) i =
      let (u0', i') = utyToTy' u0 (i + 1)
          (u1', i'') = utyToTy' u1 i'
       in (TDepFn ("inf.dep." ++ show i) u0' u1', i'')

unifTyToTy :: UnifType -> Type
unifTyToTy = error "unifyTytyTy unimplemented"

subTerm :: Subst -> Term -> Term
subTerm s (TLet v t0 t1) = TLet v (subTerm s t0) (subTerm s t1)
subTerm s (TLam v t) = TLam v (subTerm s t)
subTerm s (TApp t v) = TApp (subTerm s t) v
subTerm s (TAnn t ty) = TAnn (subTerm s t) (subTyp s ty)
subTerm s (TCond v t1 t2) = TCond v (subTerm s t1) (subTerm s t2)
subTerm s (TRec v t1 ty t2) = TRec v (subTerm s t1) (subTyp s ty) (subTerm s t2)
subTerm s t = t

showUnify :: Program -> IO ()
showUnify = print . unify . preprocessVariables . fst . constrain

explicitSigs :: Subst -> Program -> Program
explicitSigs s p = decls %~ const newdtbl $ p
  where
    newdtbl = foldl (\tsf (fn, ft) -> tblSet fn ft tsf) (p ^. decls) newDecls
    newDecls = mapMaybe getOrMakeDecl (bToList (p ^. bodies . dom))
    getOrMakeDecl fn
      | bContains fn (p ^. decls . dom) = Nothing
      | otherwise = case findRoot (UFnR fn) s of
          (Left uv) -> Just (fn, uvToTy uv)
          (Right uty) -> Just (fn, utyToTy uty)

rewriteTypes :: Subst -> Program -> Program
rewriteTypes s = decls %~ fmap (explicitforall . subTyp s)
  where
    explicitforall :: Type -> Type
    explicitforall t = doit (tyQuant t) t

    doit [] t = t
    doit (n : ns) t = TForall n BaseKind $ doit ns t

-- Canonical quantification over type variables in a term.

tyQuant :: Type -> [String]
tyQuant (TRBase (BTVar v) _) = [v]
tyQuant (TDepFn _ t0 t1) = nub $ tyQuant t0 ++ tyQuant t1
tyQuant _ = []

rewriteTerms :: Subst -> Program -> Program
rewriteTerms = error "rewrite terms unimplemented"
  where
    -- uh oh... how to we do the explicit type application?
    -- We hav e the function type written down

    rewriteTerm :: Subst -> Term -> Term
    rewriteTerm s k@(TConst _) = k
    rewriteTerm s v@(TVar _) = v
    rewriteTerm s (TLet v t1 t2) = TLet v (rewriteTerm s t1) (rewriteTerm s t2)
    rewriteTerm s (TLam v t) = TLam v (rewriteTerm s t)
    rewriteTerm s (TApp (TAnn t barety) v) = TApp (mk bare real t) v
      where
        bare = subTyp s bare
        -- Get the real type for this function call
        real = todo
        -- (if it's at a top-level definition only!)
        -- Make a type application sequence that meets the requirements of the real type
        -- Insert holes, too.
        -- (otherwise, just do nothing. It ain't polymorphic.  )
        mk :: Type -> Type -> Term -> Term
        mk annTyp realTyp t0 = todo
    rewriteTerm s (TAnn t ty) = TAnn (rewriteTerm s t) (subTyp s ty)
    rewriteTerm s (TCond v tt tf) = TCond v (rewriteTerm s tt) (rewriteTerm s tf)
    rewriteTerm s (TRec v t1 ty t2) = error "letrec is unsupported"

-- Rewrite the program to
-- todo: infer all free variables too!
--  DONE 0. Add extra annotations for the functions without type signautures
--  DONE 1. Apply the subtitutions to all type signatures and bodies
--  DONE 2. Add explicit forall's to all function signatures
--       2.1. Add explicit term-level type abstraction at the start of functiona
--  DONE 2.2. Add explicit term-level type applications at call sites (with holes)
rewrite :: Program -> Arity -> Subst -> Program
rewrite = todo

infer :: Program -> Program
infer = todo
