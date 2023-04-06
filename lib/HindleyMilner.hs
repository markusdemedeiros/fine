{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use record patterns" #-}
module HindleyMilner where

import BasicChecker (BasicType (..), FnName, Program, Refinement (..), Term (..), Type (..), Variable, base, bodies, decls, prim)
import Control.Lens (Bifunctor (bimap), over, (%~), (^.))
import Control.Monad
import qualified Control.Monad.State as ST
import Data.Functor ((<&>))
import Data.Maybe (catMaybes, mapMaybe)
import GHC.Generics (UInt)
import Surface (fn, tyv)
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

gensym :: ConstraintST UnifVar
gensym = do
  r <- ST.get
  ST.put (r + 1)
  return $ Anon r

collectArity :: Program -> Arity
collectArity p = def %~ const (Just 1) $ typeArity <$> (p ^. decls)
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
      | (a + 1) == n = UnifVar $ FnVal name
      | (a + 1) < n = UnifFn (UnifVar (FnArg name a)) $ mkty (a + 1) n

-- Convert a type into its base form
eraseRefinements :: Type -> UnifType
eraseRefinements (TRBase b _) = UnifVar $ UnifAtom b
eraseRefinements (TDepFn _ t1 t2) = UnifFn (eraseRefinements t1) (eraseRefinements t2)
eraseRefinements (TForall _ _ _) = error "illegal type quantifier in erase refinements"

type Gamma = Table Variable UnifType

-- Get constraints for a single body
-- Synthesize the entire most general type, and constrain it to be equal to (declType)
synTerm :: Arity -> FnName -> Term -> ConstraintST [UnifConstraint]
synTerm a name term = do
  (tau, cs) <- j (emptyTable Nothing) term
  return $ (declType a name, tau) : cs
  where
    -- Extends Algorithm J
    -- Does not implement let-polymorphism
    -- https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
    j :: Gamma -> Term -> ConstraintST (UnifType, [UnifConstraint])

    -- Constants: Match base type of primitve type
    j g (TConst k) = return (eraseRefinements $ prim k, [])
    -- Variables:
    --    If v is free, return the declType.
    --    If v is bound, lookup the type in the context.
    --    No new constraints in either case.
    j g (TVar v)
      | bContains v (g ^. dom) = return (getTbl g v, [])
      | otherwise = return (declType a v, [])
    -- Let bindings:
    --  For now, we're going to do this the same as lambda. No let-polymorphism.
    j g (TLet x bound body) = do
      (te, ce) <- j g bound
      (tb, cb) <- j (tblSet x te g) body
      return (tb, ce ++ cb)
    -- Lambda bindings:
    --  Allocate fresh unification variable tau
    --  Set x to tau in g, check the body to get tau'
    --  Result is tau->tau'; no new bindings.
    j g (TLam x body) = do
      tau <- gensym <&> UnifVar
      (tau', cs) <- j (tblSet x tau g) body
      return (UnifFn tau tau', cs)
    -- Annotations:
    --  Get the type of the inner term
    --  Constrain that type to the annotation
    --  Return the preferred type (the annotation)
    j g (TAnn t typ) = do
      (tau, cs) <- j g t
      return (eraseRefinements typ, (eraseRefinements typ, tau) : cs)
    j g (TApp e varg) = do
      (tauFunction, cf) <- j g e
      tauArg <- j g (TVar varg) <&> fst
      tauResult <- gensym <&> UnifVar
      return (tauResult, (UnifFn tauArg tauResult, tauFunction) : cf)

    -- Conditionals:
    --  Get the types of all three subterms
    --  Constrain the predicate type to be a boolean
    --  Contrain the tt and tf types to be equal (prefer tt)
    j g (TCond vc tt tf) = do
      -- It is sound to treat vc as if it was a variable term here.
      (tauc, cc) <- j g (TVar vc)
      (taut, ct) <- j g tt
      (tauf, cf) <- j g tf
      let condPred = (tauc, UnifVar . UnifAtom $ BBool)
      let branchPred = (taut, tauf)
      return (taut, condPred : branchPred : (cc ++ ct ++ cf))

    -- Letrec:
    --  TODO
    j g (TRec v bound ty body) = do todo
    j _ _ = error "unhandled case in algorithm j"

-- Get constraints for a single function declaration
synDecl :: Arity -> FnName -> Type -> [UnifConstraint]
synDecl a name typ = [(eraseRefinements typ, declType a name)]

-- Get all of the type inference constraints for a program
constrain :: Program -> [UnifConstraint]
constrain p = declConstraints ++ bodyConstraints
  where
    arity = collectArity p
    declConstraints = concatMap (\nm -> synDecl arity nm (getTbl (p ^. decls) nm)) (p ^. (decls . dom))
    bodyConstraints = fst . flip ST.runState 0 $ foldM (\c0 nm -> synTerm arity nm (getTbl (p ^. bodies) nm) <&> (++ c0)) [] (p ^. (bodies . dom))

-- Helpful for debugging
showConstraints :: Program -> IO ()
showConstraints p = mapM_ (putStrLn . pretty) (constrain p)
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

-- data UVar
--   = UAnon Int
--   | UFnAg FnName Int
--   | UFnR FnName
--   | UserVar String
--   deriving (Show, Eq)
--
-- -- Grounded types.
-- data UConcrete
--   = UBool
--   | UInt
--   deriving (Show, Eq)
--
-- -- Trees of types.
-- data UTy
--   = UConc UConcrete
--   | UVar UVar
--   | UFn UTy UTy
--   deriving (Show, Eq)

-- subTyp s (UnifFn uv) = todo

subTerm :: Subst -> Term -> Term
subTerm = todo

showUnify :: Program -> IO ()
showUnify = print . unify . preprocessVariables . constrain

explicitSigs :: Subst -> Program -> Program
explicitSigs s p = decls %~ const newdtbl $ p
  where
    newdtbl = foldl (\tsf (fn, ft) -> tblSet fn ft tsf) (p ^. decls) newDecls
    newDecls = mapMaybe getOrMakeDecl (bToList (p ^. (bodies . dom)))
    getOrMakeDecl fn
      | bContains fn (p ^. (decls . dom)) = Nothing
      | otherwise = case findRoot (UFnR fn) s of
          (Left uv) -> Just (fn, uvToTy uv)
          (Right uty) -> Just (fn, utyToTy uty)

rewriteTypes :: Subst -> Program -> Program
rewriteTypes s = decls %~ fmap (subTyp s)

-- Rewrite the program to
--  DONE 0. Add extra annotations for the functions without type signautures
--       1. Apply the subtitutions to all type signatures and bodies
--       2. Add explicit forall's to all function signatures
--       2.1. Add explicit term-level type abstraction at the start of functiona
--       2.2. Add explicit term-level type applications at call sites (with holes)
rewrite :: Program -> Arity -> Subst -> Program
rewrite = todo

infer :: Program -> Program
infer = todo
