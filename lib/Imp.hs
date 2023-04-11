{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Imp where

import Control.Lens (Lens', lens, makeLenses, (%~), (&), (^.))
import Data.List (intercalate)
import Debug.Trace
import Refinements
import Util

data Kappa = Kappa String (Table Var RTyp)

instance Show Kappa where
  show (Kappa n binds) = n ++ "(" ++ intercalate ", " (fmap (\v -> v ++ ": " ++ show (getTbl binds v)) (bToList (binds ^. dom))) ++ ")"

data ImpI
  = Assign Var Expr
  | Havoc Var
  | GetTuple [Var] Kappa
  | SetTuple Kappa [Var]
  | Assume Pred
  | Assert Pred
  | Then ImpI ImpI
  | Skip

instance Show ImpI where
  show (Assign v e) = v ++ " <- " ++ show e
  show (Havoc v) = "havoc " ++ v
  show (GetTuple vs kappa) = "(" ++ intercalate ", " vs ++ ") <- " ++ show kappa
  show (SetTuple kappa vs) = show kappa ++ " <- (" ++ intercalate ", " vs ++ ")"
  show (Assume p) = "assume " ++ show p
  show (Assert p) = "assert " ++ show p
  show (Then i1 i2) = "(" ++ show i1 ++ ") then " ++ show i2
  show Skip = "skip"

newtype Program = Program [ImpI]

instance Show Program where
  show (Program l) = "   " ++ intercalate "\n|| " (fmap (intercalate ";\n     " . fmap show . seqImpI) l)

seqImpI :: ImpI -> [ImpI]
seqImpI (Then i1 i2) = seqImpI i1 ++ seqImpI i2
seqImpI z = [z]

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

-- Turn a constraint set into a read-write-once constraint set
--  Everything should be cloned (that way the whole set refers to the same variable)!
--  clones only! clones 4eva!
clone :: [(G, RTyp, RTyp)] -> [(G, RTyp, RTyp)]
clone locs = locs >>= cloneBinding
  where
    cloneBinding (g, rt0, rt1) =
      let (kappaTable, rt0' : gs') = countKappas $ collectReads (g, rt0, rt1)
          rtable = makeRenameTables kappaTable
          g' = zip (fmap fst g) gs'
       in [(g', rt0', renameKappas rt1 rtbl) | rtbl <- rtable]

-- Anyways, here's a really dumb way to do this...
makeRenameTables :: Table String Int -> [Table String String]
makeRenameTables t =
  case bToList (t ^. dom) of
    [] -> [emptyTable Nothing]
    (s : _) -> [tblSet s (cloneName s z) t' | t' <- makeRenameTables (rmEntry t s), z <- [1 .. (getTbl t s)]]

renameKappas :: RTyp -> Table String String -> RTyp
renameKappas r@(RTyp _ (RP _)) _ = r
renameKappas (RTyp ty (RK s sArgs)) tbl = RTyp ty (RK nm sArgs)
  where
    nm
      | bContains s (tbl ^. dom) = getTbl tbl s
      | otherwise = cloneName s 1

-- Collect all RTyps in read position
collectReads :: (G, RTyp, RTyp) -> [RTyp]
collectReads (g, r, _) = r : fmap snd g

-- Get the list of refinement variables on the lhs of any clone (combine them with the list monad to get all possible clonings)
countKappas :: [RTyp] -> (Table String Int, [RTyp])
countKappas = foldr countR (emptyTable (Just 0), [])

-- Update the counter for a kappa, and rewrite a term to include that kappa
countR :: RTyp -> (Table String Int, [RTyp]) -> (Table String Int, [RTyp])
countR r@(RTyp _ (RP _)) (tbl, rsf) = (tbl, r : rsf)
countR (RTyp ty (RK s sArgs)) (tbl, rsf) = (tblSet s n tbl, RTyp ty (RK (cloneName s n) sArgs) : rsf)
  where
    n = 1 + getTbl tbl s

cloneName :: String -> Int -> String
cloneName s n = "clone." ++ show n ++ "." ++ s