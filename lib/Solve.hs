{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}

-- Credit: A lot of this is built off of the what4 tutorial
-- https://hackage.haskell.org/package/what4
-- Honestly I don't know shit about SMT solvers lmao

module Solve where

import Data.Foldable (forM_)
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some (..))
import System.IO (FilePath)
import What4.Config (extendConfig)
import What4.Expr
  ( BoolExpr,
    EmptyExprBuilderState (..),
    ExprBuilder,
    FloatModeRepr (..),
    GroundValue,
    groundEval,
    newExprBuilder,
  )
import What4.Interface
  ( BaseTypeRepr (..),
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

magic :: IO ()
magic = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng
  extendConfig z3Options (getConfiguration sym)
  p <- freshConstant sym (safeSymbol "p") BaseBoolRepr
  q <- freshConstant sym (safeSymbol "q") BaseBoolRepr
  r <- freshConstant sym (safeSymbol "r") BaseBoolRepr
  not_p <- notPred sym p
  not_q <- notPred sym q
  not_r <- notPred sym r
  clause1 <- orPred sym p not_q
  clause2 <- orPred sym q r
  clause3 <- orPred sym not_p not_r
  clause4 <- orPred sym not_p =<< orPred sym not_q r
  f <-
    andPred sym clause1
      =<< andPred sym clause2
      =<< andPred sym clause3 clause4
  -- Determine if f is satisfiable, and print the instance if one is found.
  checkModel
    sym
    f
    [ ("p", p),
      ("q", q),
      ("r", r)
    ]
  -- Now, let's add one more clause to f.
  clause5 <- orPred sym p =<< orPred sym q not_r
  g <- andPred sym f clause5
  checkModel
    sym
    g
    [ ("p", p),
      ("q", q),
      ("r", r)
    ]

-- | Determine whether a predicate is satisfiable, and print out the values of a
-- set of expressions if a satisfying instance is found.
checkModel ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, BoolExpr t)] ->
  IO ()
checkModel sym f es = do
  -- We will use z3 to determine if f is satisfiable.
  withZ3 sym z3executable defaultLogData $ \session -> do
    -- Assume f is true.
    assume (sessionWriter session) f
    runCheckSat session $ \result ->
      case result of
        Sat (ge, _) -> do
          putStrLn "Satisfiable, with model:"
          forM_ es $ \(nm, e) -> do
            v <- groundEval ge e
            putStrLn $ "  " ++ nm ++ " := " ++ show v
        Unsat _ -> putStrLn "Unsatisfiable."
        Unknown -> putStrLn "Solver failed to find a solution."