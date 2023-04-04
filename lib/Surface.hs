{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant $" #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Surface where
import Util

import Control.Lens (makeLenses, (^.), (%~))
import BasicChecker (Variable, Refinement (RKnown), Constant (..), Predicate (..), InterpOp (..), Term (TAnn))
import qualified Control.Monad.State as ST

-- We'll just do our "parsing" in the state monad so we can parse fresh variables and variable declarations etc.
type Srf = (SrfTerm, SrfProgram)

type ParseState = ST.State SrfProgram

parse :: ParseState SrfTerm -> Srf
parse s = ST.runState s (error "syntax error: body _main_ is not set")

-- fixme: remove naming ambiguity in the surface syntax
type FnName = String
type TyVarName = String

-- | A program consists of a sequence of declarations and bodies, followed by one untyped term. 
-- | The types and terms of reside in rank 1 system F. 
data SrfProgram
  = SrfProgram {_decls :: Table FnName SrfType, _bodies :: Table FnName SrfTerm}
  deriving (Show, Eq)

data STRBaseType
  = SBool
  | SInt
  | SVal TyVarName
  deriving (Show, Eq)

data SrfType
  = STRBase STRBaseType Refinement
  | STRFn Variable SrfType SrfType
  deriving (Show, Eq)

data SrfTerm
  = SRTConst Constant
  | SRTVar Variable
  | SRTLet Variable SrfTerm SrfTerm
  | SRTLam Variable SrfTerm
  | SRTApp SrfTerm Variable
  | SRTAnn SrfTerm SrfType
  | SRTCond Variable SrfTerm SrfTerm
  | SRTRec Variable SrfTerm SrfType SrfTerm
  deriving (Show, Eq)

makeLenses ''SrfProgram


-- | program position

_val :: FnName -> SrfType -> ParseState ()
_val name typ = do
  ST.modify (decls %~ tblSet name typ)
  return ()

_let :: FnName -> [Variable] -> SrfTerm -> ParseState ()
_let name args trm = do
  ST.modify (bodies %~ tblSet name (mkTerm args trm))
  return ()
  where
    mkTerm [] t = t
    mkTerm (v : vs) t = SRTLam v (mkTerm vs t)

_main :: SrfTerm -> ParseState SrfTerm
_main = return


-- | Type position
bool :: SrfType
bool = STRBase SBool (RKnown "unused" (PBool True))

int :: SrfType
int = STRBase SBool (RKnown "unused" (PBool True))

tyv :: TyVarName -> SrfType
tyv v = STRBase (SVal v) (RKnown "unused" (PBool True))

fn :: SrfType -> SrfType -> SrfType
fn = STRFn "unused"

refn :: Variable -> SrfType -> SrfType -> SrfType
refn = STRFn


-- refine a type 
-- disallow refinements of non-base types at parse time
refine :: SrfType -> Variable -> Predicate -> SrfType
refine (STRBase b (RKnown _ (PBool True))) v p = STRBase b (RKnown v p)
refine _ _ _ = error "parse error: refinement type with nontrivial refinement"

-- | Predicate position 

var' :: Variable -> Predicate
var' = PVar

neg' :: Predicate -> Predicate
neg' = PNeg

eq', add', sub', leq', geq', lt', gt', and', or':: Predicate -> Predicate -> Predicate
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
var :: Variable -> SrfTerm
var = SRTVar

integer :: Int -> SrfTerm
integer = SRTConst . CNInt

bind :: Variable -> SrfTerm -> SrfTerm -> SrfTerm
bind = SRTLet

letrec :: Variable -> SrfTerm -> SrfType -> SrfTerm -> SrfTerm
letrec = SRTRec

cond :: Variable -> SrfTerm -> SrfTerm -> SrfTerm
cond = SRTCond

false, true :: SrfTerm
false = SRTConst (CNBool False)
true = SRTConst (CNBool True)

eq, add, sub, leq, geq, lt, gt :: SrfTerm -> SrfTerm -> SrfTerm
eq  = mkBinop $ SRTConst (CNOp Equal)
add = mkBinop $ SRTConst (CNOp Add)
sub = mkBinop $ SRTConst (CNOp Sub)
leq = mkBinop $ SRTConst (CNOp Leq)
geq = mkBinop $ SRTConst (CNOp Geq)
lt  = mkBinop $ SRTConst (CNOp Lt)
gt  = mkBinop $ SRTConst (CNOp Gt)
-- neg, and, or

mkBinop :: SrfTerm -> SrfTerm -> SrfTerm -> SrfTerm
mkBinop op a b = SRTLet "opA" a $ SRTLet "opB" b $ SRTApp (SRTApp op "opA") "opB"


-- | My "surface" syntax Srf
-- | A program is a list of declarations that ends in decl_main

prog1 :: Srf
prog1 = parse $ do
    _val "assert" $ fn (refine bool "b" (var' "b")) int
    _let "assert" ["b"] $
       integer 0

    _val "not" $ refn "x" bool (refine bool "b" (eq' (var' "b") (neg' (var' "x"))))
    _let "not" ["x"] $
      cond "x"
        false 
        true

    _val "and" $ refn "x" bool (refn "y" bool (refine bool "b" (eq' (var' "b") (and' (var' "x") (var' "y")))))
    _let "and" ["x", "y"] $
      cond "x"
        (var "y")
        false

    _val "or" $ refn "x" bool (refn "y" bool (refine bool "b" (eq' (var' "b") (or' (var' "x") (var' "y")))))
    _let "or" ["x", "y"] $
      cond "x"
        true
        (var "y")

    -- _val "abs" $ refn "x" int (refine int "v" (leq' (int' 0) (var' "v")))
    -- _let "abs" ["x"] $
    --   bind "c" todo $
    --   cond "c"
    --     todo
    --     todo
    _main $
      todo