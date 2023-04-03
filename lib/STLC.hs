module STLC where

import Refinements (Var)


data Constant
  = COp ()
  | CInt Int
  | CBool Bool

data BaseTy
  = BInt
  | BBool

data SyntaxType
  = Hole BaseTy
  | Base BaseTy
  | Ref BaseTy

data Term ty ann
  = LConst ann Constant
  | LVar ann Var
  | LLet ann Var (Term ty ann) (Term ty ann)
  | LLam ann Var (Term ty ann)
  | LApp ann (Term ty ann) Var
  | LAnn ann (Term ty ann) ty
  | LIf ann Var (Term ty ann) (Term ty ann)
  | LRec ann Var (Term ty ann) ty (Term ty ann)

type UserLevelTerm = Term SyntaxType ()

-- 1. HM Inference: Get a base type (with holes) for everything

type HMTerm = Term () ()

-- 2. Replace the holes with appropriate kappa's

type TermHoles = Term () ()

-- 3. Check the holes to get a system of constraints in the refinement logic

-- 4. Do the abstract interpretation

-- 5. Insert the new types back into the system (triangle)

-- 6. Do the checking to get a SMT clause

-- 7. Call What4 to solve it