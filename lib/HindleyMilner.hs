module HindleyMilner where

import BasicChecker (BasicType, FnName, Program, Term, Type (..), decls)
import Control.Lens (over, (%~), (^.))
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
type UnifConstraint = (UnifType, UnifType)

-- Number of arguments for all interp. and uninterp. functions.
-- This serves as a lower bounds on function arities, and (inclues return type. )
-- If the function is in the domain of the Arity table, it has a declared signaure. Otherwise,
--    it either has a binding, or is free (cool!)
-- For functions with a declared type, we get the arity from the number of right branches.
-- For functions with no declared type, their arity is at least 1. Unification will find the precise number.
type Arity = Table FnName Int

collectArity :: Program -> Arity
collectArity p = def %~ const (Just 1) $ typeArity <$> (p ^. decls)
  where
    typeArity :: Type -> Int
    typeArity (TRBase {}) = 1
    typeArity (TDepFn _ _ t) = 1 + typeArity t
    typeArity (TForall {}) = error "illegal type quantifier"

-- Get the type associated to a named function
declType :: Arity -> FnName -> UnifType
declType arity name = mkty 0 (getTbl arity name)
  where
    mkty :: Int -> Int -> UnifType
    mkty a n
      | (a + 1) == n = UnifVar $ FnVal name
      | (a + 1) < n = UnifFn (UnifVar (FnArg name a)) $ mkty (a + 1) n

-- Get constraints for a single body
synTerm :: Arity -> Term -> [UnifConstraint]
synTerm = todo

-- Get constraints for a single function declaration
synDecl :: Arity -> Term -> [UnifConstraint]
synDecl = todo

infer :: Program -> Program
infer = todo
