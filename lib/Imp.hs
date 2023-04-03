{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE TemplateHaskell #-}

module Imp where

import Refinements
import Util
import Control.Lens (Lens', lens, makeLenses, (%~), (&), (^.))

newtype Kappa a = Kappa [(Var, a)]

data ImpI
  = Assign Var Expr
  | Havoc Var
  | GetTuple [Var] (Kappa Expr)
  | SetTuple (Kappa Expr) [Var]
  | Assume Pred
  | Assert Pred
  | Then ImpI ImpI

newtype Program = Program [ImpI]


-- | Relational Semantics

data IStateR v = IStateR { _vars :: Table Var v, _rels :: Table Var (BSet [v])}

makeLenses ''IStateR

type StateR v = Maybe (IStateR v)

