module Refinements where


-- | Constraint system for refinement types 
-- | Top-level program should produce this

-- | simple uninterpreted type variables
type Uninterp = String

-- | complex uninterpreted types
data Cu 
  = V Uninterp
  | F [Cu] Cu

-- | types
data Typ
  = I Int 
  | B Bool
  | C Cu

-- | representation of variables from the syntax
type Var = String

binder :: Var
binder = "nu"

-- | type enviornments
type Env = [(Var, Typ)]

-- | predicate expressions
data Expr 
  = EV Var
  | EN Int 
  | EA Expr Expr
  | EM Int Expr
  | EF Var [Expr]

data InterpOp
  = Equal
  | Add
  | Sub
  | Leq
  | Lt
  | Geq
  | Gt
  deriving (Eq)

-- | predicates
-- data Pred
--   = PEq Expr Expr
--   | PNot Pred
--   | PAnd Pred Pred
--   | PImp Pred Pred

data Pred
  = PVar Var
  | PBool Bool
  | PInt Int
  | PInterpOp InterpOp Pred Pred
  | PAnd Pred Pred
  | POr Pred Pred
  | PNeg Pred
  | PIf Pred Pred Pred
  | PUninterpFun Var Pred -- ??
  deriving (Eq)


-- | refinement variables

type RefVar = String

-- | refinements

data Refinement 
  = RP Pred
  | RK RefVar

-- | refinement types

data RTyp = RTyp Typ Refinement

-- | refinement env

type G = [(Var, RTyp)]



