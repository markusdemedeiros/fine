{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module Refinements where

import Control.Lens.Operators ((^.))
import Data.List (intercalate)
import Util (Table, bToList, dom, getTbl)

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
  = I -- Int
  | B -- Bool
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
  | EA Expr Expr -- Add
  | EM Int Expr -- Multiply
  | EF Var [Expr]

instance Show Expr where
  show (EV v) = v
  show (EN i) = show i
  show (EA e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ") "
  show (EM i e) = "(" ++ show i ++ " * " ++ show e ++ ") "
  show (EF f vs) = f ++ "(" ++ intercalate ", " (fmap show vs) ++ ") "

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
  | PUninterpFun Var Pred -- ??
  deriving (Eq)

-- | refinements
data Refinement
  = RP Pred
  | RK String (Table Var RTyp)

-- | refinement types
data RTyp = RTyp Typ Refinement

-- | refinement env
type G = [(Var, RTyp)]

-- | subtype constraint
data SubC = SubC G RTyp RTyp

instance Show SubC where
  show (SubC g t0 t1) = "[" ++ intercalate ", " (fmap (\(v, t) -> v ++ ": " ++ show t) g) ++ "] |- " ++ show t0 ++ " <: " ++ show t1

instance Show RTyp where
  show (RTyp t r) = show t ++ "{" ++ show r ++ "}"

instance Show Typ where
  show I = "int"
  show B = "bool"
  show (C cu) = show cu

instance Show Cu where
  show (V u) = u
  show (F tys tyr) = show tys ++ " --> " ++ show tyr

instance Show Refinement where
  show (RP p) = show p
  show (RK k t) = k ++ "(" ++ intercalate ", " showkappa ++ ")"
    where
      showkappa = (\arg -> arg ++ ": " ++ show (getTbl t arg)) <$> bToList (t ^. dom)

instance Show Pred where
  show (PVar v) = v
  show (PBool b) = show b
  show (PInt i) = show i
  show (PInterpOp op p1 p2) = "(" ++ show op ++ " " ++ show p1 ++ " " ++ show p2 ++ ")"
  show (PAnd p1 p2) = "(" ++ show p1 ++ " && " ++ show p2 ++ ")"
  show (POr p1 p2) = "(" ++ show p1 ++ " || " ++ show p2 ++ ")"
  show (PNeg p) = "!(" ++ show p ++ ")"
  show (PUninterpFun v p) = v ++ "(" ++ show p ++ ")"

instance Show InterpOp where
  show Equal = "="
  show Add = "+"
  show Sub = "-"
  show Leq = "<="
  show Lt = "<"
  show Geq = ">="
  show Gt = ">"