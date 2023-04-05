{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TemplateHaskell #-}

module Util where

import Control.Lens (makeLenses, (%~), (^.))
import Control.Lens.Getter (Getter (..), to)
import Data.List (intercalate, nub)
import Data.Maybe
import Debug.Trace

todo = error "explicit todo encountered"

-------------------------------------------------------------------------------
------- Bastardized Sets and Maps

-- MY SETS WILL NEVER BE HASH SETS
-- THEY WILL NEVER BOW TO YOUR CRAVEN, CAPITALISTIC, EFFICINCY FETISH
-- FUCK THE PIGS // LISTS 4 LYFE

-- Bastardized Set
data BSet a where
  BSet :: [a] -> BSet a

bFromList :: Eq a => [a] -> BSet a
bFromList = BSet . nub

bToList :: BSet a -> [a]
bToList (BSet l) = l

bEmpty :: BSet a
bEmpty = BSet []

bContains :: (Eq a) => a -> BSet a -> Bool
bContains x (BSet l) = x `elem` l

bInsert :: (Eq a) => a -> BSet a -> BSet a
bInsert x s@(BSet l)
  | x `elem` l = s
  | otherwise = BSet (x : l)

-- bask in the heat radiating off of you cpu
-- feel the joyful glow of being free from (Hashable a) and (Ord a)
bUnion :: (Eq a) => BSet a -> BSet a -> BSet a
bUnion (BSet []) x = x
bUnion (BSet (l : ls)) x = bUnion (BSet ls) (bInsert l x)

instance Functor BSet where
  fmap :: (a -> b) -> BSet a -> BSet b
  fmap f (BSet l) = BSet (fmap f l)

instance (Eq a) => Eq (BSet a) where
  (==) (BSet l0) (BSet l1) = all (`elem` l1) l0 && all (`elem` l0) l1

instance Foldable BSet where
  foldr f s0 (BSet l) = foldl (flip f) s0 (BSet (reverse l))

  foldl :: (b -> a -> b) -> b -> BSet a -> b
  foldl _ s0 (BSet []) = s0
  foldl accFn s0 (BSet (a0 : as)) = foldl accFn (accFn s0 a0) (BSet as)

instance (Show a) => Show (BSet a) where
  show (BSet l) = "{ " ++ intercalate ", " (fmap show l) ++ " }"

-------------------------------------------------------------------------------
------- Finite Types

class Finite a where
  -- Enumerate a finite set of possible values in this domain.
  domain :: BSet a

  -- Efficiently override set containment in (domain :: S.Set a).
  contains :: a -> Bool

-------------------------------------------------------------------------------
------- Functional Tables

data Table d r = Table {_dom :: BSet d, _map :: d -> r, _def :: Maybe r}

makeLenses ''Table

-- def is a an option this table returns
-- if def is not None, all out of scope

instance Functor (Table d) where
  fmap :: (a -> b) -> Table d a -> Table d b
  fmap f (Table dom m def) = Table dom (f . m) (fmap f def)

instance (Show d, Show r) => Show (Table d r) where
  show t@(Table dom fun def) =
    "[ " ++ (drop 2 . reverse . drop 1 . reverse) (concatMap (\x -> "  (" ++ show x ++ " -> " ++ show (fun x) ++ ")\n\t\t ") dom ++ ds) ++ "]"
    where
      ds = case def of
        Nothing -> ""
        (Just x) -> "  (_ -> " ++ show x ++ ") \n"

getDom :: Table d r -> BSet d
getDom (Table d _ _) = d

getRng :: Table d r -> BSet r
getRng (Table d m _) = fmap m d

getDef :: Table d r -> Maybe r
getDef (Table _ _ d) = d

-- Gets a partial function that looks up table entries
getTbl :: (Eq d, Show d) => Table d r -> (d -> r)
getTbl (Table dom m def) d
  | bContains d dom = m d
  | otherwise =
      case def of
        (Just r) -> r
        Nothing -> error $ "lookup of [" ++ show d ++ "] failed in a table with domain " ++ show dom

-- Empty table with empty domain.
emptyTable :: Maybe r -> Table d r
emptyTable = Table bEmpty (const (error "somehow managed to do a bad lookup"))

-- Set a value in a table, possibly updating the domain.
tblSet :: (Eq d, Show d) => d -> r -> Table d r -> Table d r
tblSet d r (Table dom fun def) = Table (bInsert d dom) newlookup def
  where
    newlookup k
      | k == d = r
      | otherwise = fun k

-- Check pointwise equality between tables.
--    Their domains must be equal, and
--    Their mappings must be equal on their domains.
instance (Eq d, Eq r, Show d) => Eq (Table d r) where
  (==) (Table dom0 fun0 def0) (Table dom1 fun1 def1) =
    deq && veq
    where
      -- trace ("[tbl ==] " ++ show deq ++ " " ++ show veq ++ " " ++ show defeq) $ deq && veq -- && defeq

      deq = (dom0 == dom1)
      veq = all (\s -> fun0 s == fun1 s) dom0
      defeq = (def0 == def1)
