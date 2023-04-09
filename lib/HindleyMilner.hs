{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use record patterns" #-}
module HindleyMilner where

import BasicChecker (BasicType (..), FnName, Kind (..), Predicate (PBool), Program, Refinement (..), Term (..), Type (..), Variable, base, bodies, decls, prim)
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
  deriving (Eq)

instance Show UnifVar where
  show (UnifAtom b) = show b
  show (Anon i) = "tmp." ++ show i
  show (FnArg name i) = name ++ ".arg." ++ show i
  show (FnVal name) = name ++ ".val"

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

genunused :: ConstraintST String
genunused = do
  r <- ST.get
  ST.put (r + 1)
  return $ "unused." ++ show r

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
collectArity p = foldl (\tsf bodynm -> tblSet bodynm (termArity (getTbl (p ^. bodies) bodynm)) tsf) typeTbl (bToList $ p ^. (bodies . dom))
  where
    typeTbl = def %~ const (Just 1) $ typeArity <$> p ^. decls

    typeArity :: Type -> Int
    typeArity (TRBase {}) = 1
    typeArity (TDepFn _ _ t) = 1 + typeArity t
    typeArity (TForall {}) = error "illegal type quantifier in typeArity"

    termArity :: Term -> Int
    -- termArity (TLam _ t) = 1 + termArity t
    termArity _ = 1

-- Get the type associated to a named function
declType :: Arity -> FnName -> UnifType
declType arity name = mkty 0 (getTbl arity name)
  where
    mkty :: Int -> Int -> UnifType
    mkty a n
      | a + 1 == n = UnifVar $ FnVal name
      | a + 1 < n = UnifFn (UnifVar (FnArg name a)) $ mkty (a + 1) n

-- Get the list of all polymorphic type variables in order
-- polyTyp :: Type -> [(BasicType, Maybe String)]
-- polyTyp (TRBase _ _) f = mklist []
-- polyTyp (TDepFn _ x y) =
--   = TRBase BasicType Refinement
--   | TDepFn Variable Type Type

-- Convert a type into its base form
eraseRefinements :: Type -> UnifType
eraseRefinements (TRBase b _) = UnifVar $ UnifAtom b
eraseRefinements (TDepFn _ t1 t2) = UnifFn (eraseRefinements t1) (eraseRefinements t2)
eraseRefinements (TForall {}) = error "illegal type quantifier in erase refinements"

type Gamma = Table Variable UnifType

explicateQuantifiers :: Type -> Term -> Term
explicateQuantifiers (TForall alpha k t) trm = TTAbs alpha k (explicateQuantifiers t trm)
explicateQuantifiers _ trm = trm

-- Generate constraints that enforece that the inferred type is the same as the declared one
-- Arguments:
--    Inferred type at the top-level
--    Declared type
--    Map between declared polymorphic types and top-levl UnifVars
enforceDecl :: UnifType -> Type -> [UnifConstraint]
enforceDecl uty (TRBase b _) = [(uty, UnifVar . UnifAtom $ b)]
enforceDecl uty (TForall _ _ t) = enforceDecl uty t
enforceDecl (UnifFn t1 t2) (TDepFn _ ta tb) = enforceDecl t1 ta ++ enforceDecl t2 tb

-- Get constraints for a single body
-- Synthesize the entire most general type, and constrain it to be equal to (declType)
-- When fresh variables are generated, we also rewrite the program with explicit annotations.
synTerm :: Table FnName Type -> FnName -> Term -> ConstraintST ([UnifConstraint], Term)
synTerm a name term = do
  (tau, bodyConstraints, tbody) <- j (emptyTable Nothing) term
  let declaredType = getTbl a name
  let declConstraints = enforceDecl tau declaredType
  return (declConstraints ++ bodyConstraints, explicateQuantifiers declaredType tbody)
  where
    -- Extends Algorithm J
    -- Does not implement let-polymorphism
    -- https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
    j :: Gamma -> Term -> ConstraintST (UnifType, [UnifConstraint], Term)

    -- Constants: Match base type of primitve type
    j g x@(TConst k) = return (eraseRefinements $ prim k, [], x)
    -- Variables:
    --    If v is free, return the declType.
    --      1. Make fresh type variables according to the signature of the decltype
    --      2. Rewrite the program so that it explicitly applies these signautres to the decltype
    --    If v is bound, lookup the type in the context.
    --    No new constraints in either case.
    j g x@(TVar v)
      | bContains v (g ^. dom) = return (getTbl g v, [], x)
      | otherwise = globalAssignment (getTbl a v) (emptyTable Nothing) (TVar v)
      where
        -- Recurse through the target type
        --  - Each forall generates a new fresh type variables
        --  - The final type substitutes all of those type variables in the declared type
        --  - The final term has explicit applications at each level
        --  - No constraints are generated
        globalAssignment :: Type -> Table String String -> Term -> ConstraintST (UnifType, [UnifConstraint], Term)
        globalAssignment (TForall alpha _ tInner) env trm = do
          tau <- genty
          globalAssignment tInner (tblSet alpha tau env) (TTApp trm (TRBase (BTVar tau) Hole))
        globalAssignment tyOpen env trm = return (tySubst tyOpen env, [], trm)

        -- Assumes the type has no quantification left in it
        -- Replace closed-over type variables with the newly generated ones
        tySubst :: Type -> Table String String -> UnifType
        tySubst (TRBase (BTVar v) _) env = UnifVar . UnifAtom . BTVar $ getTbl env v
        tySubst (TRBase BInt _) env = UnifVar . UnifAtom $ BInt
        tySubst (TRBase BBool _) env = UnifVar . UnifAtom $ BBool
        tySubst (TDepFn _ t1 t2) env = UnifFn (tySubst t1 env) (tySubst t2 env)
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

-- Get all the type inference constraints for a program due to dataflow
constrain :: Program -> (Table FnName [UnifConstraint], Program)
constrain p = (constraintTable, rewrittenProgram)
  where
    closedTypes = closeTypes p
    (constraintTable, bodyTable) = fst . flip ST.runState 0 $ foldM (\(csf, psf) nm -> synTerm closedTypes nm (getTbl (p ^. bodies) nm) >>= (\(x, y) -> return (tblSet nm x csf, tblSet nm y psf))) (emptyTable Nothing, p ^. bodies) (p ^. bodies . dom)
    rewrittenProgram = bodies %~ depFmap (\fn _ -> getTbl bodyTable fn) $ p

-- bodyConstraints = fst bodyResults
-- finalProgram = bodies %~ const (snd bodyResults) $ p
-- bodyResults = fst . flip ST.runState 0 $ foldM (\(csf, psf) nm -> synTerm (p ^. decls) nm (getTbl (p ^. bodies) nm) >>= (\(x, y) -> return (tblSet nm x csf, tblSet nm y psf))) (emptyTable Nothing, p ^. bodies) (p ^. bodies . dom)

explicitTypes :: Arity -> Program -> Program
explicitTypes a p = decls %~ const newDecls $ p
  where
    newDecls = foldl (\declSF freeVar -> tblSet freeVar (generateType freeVar) declSF) (p ^. decls) toGenerateFor

    -- List of global functions that need types generated for them
    toGenerateFor = filter (\fn -> not (bContains fn (p ^. (decls . dom)))) (bToList $ bUnion freevars (p ^. (bodies . dom)))

    -- Make a fully polymorphic type with unused type variables
    generateType :: FnName -> Type
    generateType f = g' 0 $ declType a f
      where
        g' :: Int -> UnifType -> Type
        g' _ (UnifVar v) = TRBase (BTVar (f ++ ".poly." ++ show v)) (RKnown (PBool True))
        g' i (UnifFn v1 v2) =
          TDepFn
            ("unused" ++ show i)
            (TRBase (BTVar (f ++ ".poly." ++ show i)) (RKnown (PBool True)))
            (g' (i + 1) v2)

    freevars :: BSet FnName
    freevars = foldl bUnion bEmpty (fmap (freeInTerm bEmpty) (bToList (getRng $ p ^. bodies)))

    freeInTerm :: BSet String -> Term -> BSet FnName
    freeInTerm bound (TConst _) = bEmpty
    freeInTerm bound (TVar v)
      | bContains v bound = bEmpty
      | otherwise = bFromList [v]
    freeInTerm bound (TLet x b body) =
      bUnion (freeInTerm bound b) (freeInTerm (bInsert x bound) body)
    freeInTerm bound (TLam x t) = freeInTerm (bInsert x bound) t
    freeInTerm bound (TApp t _) = freeInTerm bound t
    freeInTerm bound (TAnn t _) = freeInTerm bound t
    freeInTerm bound (TCond _ t1 t2) = bUnion (freeInTerm bound t1) (freeInTerm bound t2)
    freeInTerm bound (TRec _ _ _ _) = error "letrec unsupported in freeInterm"
    freeInTerm bound (TTAbs _ _ t) = freeInTerm bound t
    freeInTerm bound (TTApp t _) = freeInTerm bound t

-- Helpful for debugging
showConstraints :: Table FnName [UnifConstraint] -> IO ()
showConstraints ctable = mapM_ (\fn -> putStrLn (" -- " ++ fn ++ ": ") >> mapM_ (putStrLn . pretty) (getTbl ctable fn)) (bToList $ ctable ^. dom)
  where
    -- (fmap pretty) (fst $ constrain p)

    -- mapM_ (putStrLn . pretty) (fst (constrain p))
    pretty :: UnifConstraint -> String
    pretty (c0, c1) = pretty' c0 ++ " = " ++ pretty' c1 ++ ";"
    pretty' (UnifVar uv) = show uv
    pretty' (UnifFn (UnifVar uv) tr) = show uv ++ " -> " ++ pretty' tr
    pretty' (UnifFn ta tr) = pretty' ta ++ " -> " ++ pretty' tr

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

-- showUnify :: Program -> IO ()
-- showUnify = print . unify . preprocessVariables . fst . constrain

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

infer :: Program -> Program
infer = todo

-- We assume all functions have a type declaration
-- Give us a set of new types
closeTypes :: Program -> Table FnName Type
closeTypes p = (\ty -> closeType (bToList $ freeTypeVariables ty) ty) <$> (p ^. decls)

closeType :: [String] -> Type -> Type
closeType tys t = foldr (`TForall` BaseKind) t tys

freeTypeVariables :: Type -> BSet String
freeTypeVariables (TRBase (BTVar alpha) _) = bFromList [alpha]
freeTypeVariables (TRBase _ _) = bFromList []
freeTypeVariables (TDepFn _ t1 t2) = bUnion (freeTypeVariables t1) (freeTypeVariables t2)
