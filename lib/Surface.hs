{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant $" #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}

module Surface where

import BasicChecker (BasicType (..), Constant (..), FnName, InterpOp (..), Predicate (..), Program, Refinement (RKnown), Term (..), Type (..), Variable, bodies, decls, emptyProgram)
import Control.Lens (makeLenses, (%~), (^.))
import qualified Control.Monad.State as ST
import Util

-- We'll just do our "parsing" in the state monad so we can parse fresh variables and variable declarations etc.
-- Types without bodies are OK (uninterpreted spec)
-- Bodies without types are OK (infer the type)
-- Users are _not_ allowed to quantify over type variables, but they are allowed write them (interp. as Rank 1 Types)
-- Users are _not_ allowed to explicitly do type abstraction or type application.
-- Users _are_ allowed to insert type holes, but not in all cases?
-- Names must obey the following conventions:
--    TODO

type ParseState = ST.State Program

-- possibly check the validity of names here
parse :: ParseState a -> Program
parse s = snd $ ST.runState s emptyProgram

-- fixme: remove naming ambiguity in the surface syntax
type TyVarName = String

-- | A program consists of a sequence of declarations and bodies, followed by one untyped term.
-- | The types and terms of reside in rank 1 system F.

-- | program position
_val :: FnName -> Type -> ParseState ()
_val name typ = do
  ST.modify (decls %~ tblSet name typ)
  return ()

_let :: FnName -> [Variable] -> Term -> ParseState ()
_let name args trm = do
  ST.modify (bodies %~ tblSet name (mkTerm args trm))
  return ()
  where
    mkTerm [] t = t
    mkTerm (v : vs) t = TLam v (mkTerm vs t)

_main :: Term -> ParseState Term
_main = return

-- | Type position
bool :: Type
bool = TRBase BBool (RKnown "unused" (PBool True))

int :: Type
int = TRBase BInt (RKnown "unused" (PBool True))

tyv :: TyVarName -> Type
tyv v = TRBase (BTVar v) (RKnown "unused" (PBool True))

fn :: Type -> Type -> Type
fn = TDepFn "unused"

refn :: Variable -> Type -> Type -> Type
refn = TDepFn

-- refine a type
-- disallow refinements of non-base types at parse time
refine :: Type -> Variable -> Predicate -> Type
refine (TRBase b (RKnown _ (PBool True))) v p = TRBase b (RKnown v p)
refine _ _ _ = error "parse error: refinement type with nontrivial refinement"

-- | Predicate position
var' :: Variable -> Predicate
var' = PVar

neg' :: Predicate -> Predicate
neg' = PNeg

eq', add', sub', leq', geq', lt', gt', and', or' :: Predicate -> Predicate -> Predicate
eq' = PInterpOp Equal
add' = PInterpOp Add
sub' = PInterpOp Sub
leq' = PInterpOp Leq
geq' = PInterpOp Geq
lt' = PInterpOp Lt
gt' = PInterpOp Gt
and' = PAnd
or' = POr

int' :: Int -> Predicate
int' = PInt

-- | Term Position
var :: Variable -> Term
var = TVar

integer :: Int -> Term
integer = TConst . CNInt

bind :: Variable -> Term -> Term -> Term
bind = TLet

lam :: Variable -> Term -> Term
lam = TLam

app :: Term -> Variable -> Term
app = TApp

letrec :: Variable -> Term -> Type -> Term -> Term
letrec = TRec

cond :: Variable -> Term -> Term -> Term
cond = TCond

false, true :: Term
false = TConst (CNBool False)
true = TConst (CNBool True)

-- eq, add, sub, leq, geq, lt, gt :: Term -> Term -> Term
-- eq = mkBinop $ TConst (CNOp Equal)
-- add = mkBinop $ TConst (CNOp Add)
-- sub = mkBinop $ TConst (CNOp Sub)
-- leq = mkBinop $ TConst (CNOp Leq)
-- geq = mkBinop $ TConst (CNOp Geq)
-- lt = mkBinop $ TConst (CNOp Lt)
-- gt = mkBinop $ TConst (CNOp Gt)

eq, add, sub, leq, geq, lt, gt :: Term
eq = TConst $ CNOp Equal
add = TConst $ CNOp Add
sub = TConst $ CNOp Sub
leq = TConst $ CNOp Leq
geq = TConst $ CNOp Geq
lt = TConst $ CNOp Lt
gt = TConst $ CNOp Gt

-- neg, and, or

mkBinop :: Term -> Term -> Term -> Term
mkBinop op a b = TLet "opA" a $ TLet "opB" b $ TApp (TApp op "opA") "opB"

-- | My "surface" syntax Srf
-- | A program is a list of declarations that ends in decl_main
prog1 :: Program
prog1 = parse $ do
  _val "assert" $ fn (refine bool "b" (var' "b")) int
  _let "assert" ["b"] $
    integer 0

  _val "not" $ refn "x" bool (refine bool "b" (eq' (var' "b") (neg' (var' "x"))))
  _let "not" ["x"] $
    cond
      "x"
      false
      true

  _val "and" $ refn "x" bool (refn "y" bool (refine bool "b" (eq' (var' "b") (and' (var' "x") (var' "y")))))
  _let "and" ["x", "y"] $
    cond
      "x"
      (var "y")
      false

  _val "or" $ refn "x" bool (refn "y" bool (refine bool "b" (eq' (var' "b") (or' (var' "x") (var' "y")))))
  _let "or" ["x", "y"] $
    cond
      "x"
      true
      (var "y")

-- _val "abs" $ refn "x" int (refine int "v" (leq' (int' 0) (var' "v")))
-- _let "abs" ["x"] $
--   bind "c" todo $
--   cond "c"
--     todo
--     todo

prog2 :: Program
prog2 = parse $ do
  _val "or" $ refn "x" bool (refn "y" bool (refine bool "b" (eq' (var' "b") (or' (var' "x") (var' "y")))))
  _let "or" ["x", "y"] $
    cond
      "x"
      true
      (var "y")

prog3 :: Program
prog3 = parse $ do
  _val "v" $ refine int "z" (eq' (var' "z") (int' 4))
  _let "main" [] $
    app (lam "x" (var "x")) "id"

prog4 :: Program
prog4 = parse $ do
  _val "x" $ fn (tyv "'a") (tyv "'b")
  -- _val "y" $ fn (tyv "'b") (tyv "'a")
  -- _val "main" $ fn (tyv "'e") (tyv "'f")
  _let "main" ["z"] $
    cond "z" (var "x") (var "y")

prog5 :: Program
prog5 = parse $ do
  _val "assert" $ refine bool "b" (var' "b")
  _let "assert" ["b"] $ integer 0

  _val "zero" $ refine int "v" (eq' (var' "v") (int' 0))

  -- explicit version (no holes)
  _val "abs" $ refn "x" int (refine int "v" (leq' (int' 0) (var' "v")))
  _let "abs" ["x"] $
    bind "c" (app (app leq "zero") "x") $
      cond
        "c"
        (var "x")
        (app (app sub "zero") "x")

  _val "main" $ fn int int
  _let "main" ["y"] $
    bind "z" (app (var "abs") "y") $
      bind "c" (app (app leq "zero") "z") $
        (app (var "assert") "z")
