{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Imp where

import Control.Lens (Lens', lens, makeLenses, (%~), (&), (^.))
import Refinements
import Util

data Kappa = Kappa String (Table Var RTyp)

data ImpI
  = Assign Var Expr
  | Havoc Var
  | GetTuple [Var] Kappa
  | SetTuple Kappa [Var]
  | Assume Pred
  | Assert Pred
  | Then ImpI ImpI
  | Skip

newtype Program = Program [ImpI]

-- | Relational Semantics
data IStateR v = IStateR {_vars :: Table Var v, _rels :: Table Var (BSet [v])}

makeLenses ''IStateR

type StateR v = Maybe (IStateR v)

-- | Constraint translation
toImp :: [(G, RTyp, RTyp)] -> Program
toImp = Program . fmap toImpBlock
  where
    toImpBlock :: (G, RTyp, RTyp) -> ImpI
    toImpBlock (g, t1, t2) =
      Then (toImpG g) $ Then (toImpGet t1) $ toImpSet t2

    toImpG :: G -> ImpI
    toImpG [] = Skip
    toImpG ((x, tau) : gs) =
      Then (toImpGet tau) $ Then (Assign x (EV binder)) $ toImpG gs

    toImpGet :: RTyp -> ImpI
    toImpGet (RTyp tau (RP p)) = Then (Havoc binder) $ Assume p
    toImpGet (RTyp tau (RK kappa substs)) =
      Then (GetTuple ts (Kappa kappa substs)) r
      where
        kDom = bToList $ substs ^. dom
        -- t_i statements, excluding t_0
        ts = ('t' :) . show <$> take (length kDom) [1 ..]
        -- all t_i statmentes
        ts' = "t0" : ts
        -- Assume statements, excluding the assume to t_0,
        assumes = reverse $ uncurry Assign <$> zip kDom (EV <$> ts)

        r :: ImpI
        r = foldl (flip Then) (Assign binder (EV "t0")) assumes

    toImpSet :: RTyp -> ImpI
    toImpSet (RTyp tau (RP p)) = Assert p
    toImpSet (RTyp tau (RK kappa substs)) = SetTuple (Kappa kappa substs) (binder : bToList (substs ^. dom))

clone :: ImpI -> ImpI
clone = todo