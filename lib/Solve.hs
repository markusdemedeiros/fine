{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- Credit: A lot of this is built off of the what4 tutorial
-- https://hackage.haskell.org/package/what4
-- Honestly I don't know shit about SMT solvers lmao

module Solve where

import BasicChecker (Constraint (..))
import qualified BasicChecker as B
import Control.Lens ((^.))
import Control.Monad
import Data.Foldable (forM_)
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some (..))
import System.IO (FilePath)
import Util (Table, bContains, bToList, dom, emptyTable, getRng, getTbl, tblSet, todo)
import What4.BaseTypes (BaseType, KnownRepr)
import What4.Config (extendConfig)
import What4.Expr
  ( BoolExpr,
    EmptyExprBuilderState (..),
    Expr,
    ExprBuilder,
    FloatModeRepr (..),
    GroundValue,
    groundEval,
    newExprBuilder,
  )
import What4.Interface
  ( BaseTypeRepr (..),
    BoundVar,
    IsExprBuilder (..),
    IsSymExprBuilder (forallPred, freshBoundVar, varExpr),
    andPred,
    freshConstant,
    getConfiguration,
    notPred,
    orPred,
    safeSymbol,
  )
import What4.Protocol.SMTLib2
  ( assume,
    runCheckSat,
    sessionWriter,
  )
import What4.Solver
  ( SatResult (..),
    defaultLogData,
    withZ3,
    z3Options,
  )

z3executable :: FilePath
z3executable = "z3"

type UniquifyState x = (x, Int, Table String (String, B.BasicType))

magic :: Constraint -> IO ()
magic k = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng
  extendConfig z3Options (getConfiguration sym)

  -- Generate symbols
  -- I'm storing these in a tuple of tables because I can't get the types to match! yay!
  let (uniqueC, _, cTable) = uniquifyConstraint (k, 0, emptyTable Nothing)
  -- symtables <-
  --   foldM
  --     ( \tsf (name, bty) ->
  --         case bty of
  --           B.BInt -> do
  --             s <-
  --             return (tblSet name s tsf)
  --           B.BBool -> do
  --             s <- freshBoundVar sym (safeSymbol name) BaseBoolRepr
  --             return (tblSet name s tsf)
  --           (B.BTVar x) -> error $ "type variable " ++ x ++ " not instantiated before solving"
  --     )
  --     (emptyTable Nothing)
  --     (bToList $ getRng cTable)
  cbody <- genConstraint cTable sym k

  -- verification condition: check to see if a counterexample exists
  cvc <- notPred sym cbody

  withZ3 sym z3executable defaultLogData $ \session -> do
    assume (sessionWriter session) cvc
    runCheckSat session $ \result ->
      case result of
        Sat (_, _) -> putStrLn "Type error, please click https://www.youtube.com/watch?v=dQw4w9WgXcQ as punishment. "
        Unsat _ -> putStrLn "Type check, please click https://www.youtube.com/watch?v=dQw4w9WgXcQ as reward."
        Unknown -> putStrLn "Solver failed, please click https://www.youtube.com/watch?v=dQw4w9WgXcQ to solve the halting problem."
  where
    genConstraint ts sym (CAnd c1 c2) = do
      c1' <- genConstraint ts sym c1
      c2' <- genConstraint ts sym c2
      orPred sym c1' c2'
    genConstraint ts sym (CPred p) = genPredBool sym todo p
    genConstraint ts sym (CFun v bty p c) = do
      p' <- genPredBool sym todo p
      c' <- genConstraint ts sym c
      impl <- impliesPred sym p' c'
      case bty of
        B.BBool -> do
          bv <- freshBoundVar sym (safeSymbol v) BaseBoolRepr
          forallPred sym bv impl
        B.BInt -> do
          bv <- freshBoundVar sym (safeSymbol v) BaseIntegerRepr
          forallPred sym bv impl

    genPredBool sym vts (B.PVar v) = do
      bv <- freshBoundVar sym (safeSymbol v) BaseBoolRepr
      return $ varExpr sym bv
    genPredBool sym vts (B.PBool True) = return $ truePred sym
    genPredBool sym vts (B.PBool False) = return $ falsePred sym
    genPredBool sym vts (B.PInterpOp op p1 p2) = error "interp ops brokey"
    genPredBool sym vts (B.PAnd p1 p2) = do
      p1' <- genPredBool sym vts p1
      p2' <- genPredBool sym vts p2
      andPred sym p1' p2'
    genPredBool sym vts (B.POr p1 p2) = do
      p1' <- genPredBool sym vts p1
      p2' <- genPredBool sym vts p2
      orPred sym p1' p2'
    genPredBool sym vts (B.PNeg p) = do
      p' <- genPredBool sym vts p
      notPred sym p'
    genPredBool sym vts (B.PUninterpFun f p) = error "uninterpreted function verification is broken please verify something simpler tysm"
    genPredBool sym vts (B.PHornApp _ _) = error "plz apply your horn variables"

    genPredInt sym vts (B.PVar v) = do
      bv <- freshBoundVar sym (safeSymbol v) BaseIntegerRepr
      return $ varExpr sym bv
    genPredInt sym vts (B.PInt i) = intLit sym (toInteger i)
    genPredInt sym vts (B.PInterpOp op p1 p2) = error "interp ops brokey"
    genPredInt sym vts (B.PUninterpFun f p) = error "uninterpreted function verification is broken please verify something simpler tysm"
    genPredInt sym vts (B.PHornApp _ _) = error "plz apply your horn variables"

    -- Rewrite the program to avoid scoping problems (use a monad idiot)
    -- Return the new list of variables
    uniquifyConstraint :: UniquifyState Constraint -> UniquifyState Constraint
    uniquifyConstraint (CAnd c1 c2, i, t) =
      let (c1', i', t') = uniquifyConstraint (c1, i, t)
          (c2', i'', t'') = uniquifyConstraint (c2, i', t')
       in (CAnd c1' c2', i'', t'')
    setPredVariables (CPred p, i, t) =
      let (p', i', t') = uniquifyPred (p, i, t)
       in (CPred p', i', t')
    setPredVariables (CFun v bty p c, i, t) =
      let v' = "uv" ++ show i ++ "." ++ v
          i' = i + 1
          t' = tblSet v (v', bty) t
          (p', i'', t'') = uniquifyPred (p, i', t')
          (c', i''', t''') = uniquifyConstraint (c, i'', t'')
       in (CFun v' bty p' c', i''', t''')

    -- use a monad dumbass
    -- also this doesn't need i because it doesn't generate fresh bindings
    uniquifyPred :: UniquifyState B.Predicate -> UniquifyState B.Predicate
    uniquifyPred (B.PVar v, i, t) = (B.PVar (fst $ getTbl t v), i, t)
    uniquifyPred (B.PInterpOp iop p1 p2, i, t) =
      let (p1', i', t') = uniquifyPred (p1, i, t)
          (p2', i'', t'') = uniquifyPred (p2, i', t')
       in (B.PInterpOp iop p1' p2', i'', t'')
    uniquifyPred (B.PAnd p1 p2, i, t) =
      let (p1', i', t') = uniquifyPred (p1, i, t)
          (p2', i'', t'') = uniquifyPred (p2, i', t')
       in (B.PAnd p1' p2', i'', t'')
    uniquifyPred (B.POr p1 p2, i, t) =
      let (p1', i', t') = uniquifyPred (p1, i, t)
          (p2', i'', t'') = uniquifyPred (p2, i', t')
       in (B.POr p1' p2', i'', t'')
    uniquifyPred (B.PNeg p, i, t) =
      let (p', i', t') = uniquifyPred (p, i, t)
       in (B.PNeg p', i', t')
    uniquifyPred (B.PUninterpFun f p, i, t) =
      let (p', i', t') = uniquifyPred (p, i, t)
       in (B.PUninterpFun f p', i', t')
    uniquifyPred (B.PHornApp _ _, _, _) = error "all horn variables should be applied before solving"
    uniquifyPred z = z
