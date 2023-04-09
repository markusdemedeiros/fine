module DebugMode where

import BasicChecker (Program)
import HindleyMilner (collectArity, constrain, preprocessVariables, showConstraints, unify)
import System.Process
import Util (todo)

debugMode :: Program -> IO ()
debugMode p = do
  callCommand "cowsay I wonder what stupid thing you did this time"
  srfProgram p
  doRepl
  where
    doRepl = do
      msg "options"
      putStrLn " - (i)nput program"
      putStrLn " - function (a)rities"
      putStrLn " - (c)onstraints (Hindley Milner)"
      -- putStrLn " - (u)nification (HM)"
      putStrLn " - e(x)it"
      putStr "> "
      cmd <- getLine
      putStrLn ""
      case cmd of
        "i" -> srfProgram p >> doRepl
        "a" -> srfArity p >> doRepl
        "c" -> srfConstraints p >> doRepl
        -- "u" -> srfUnify p >> doRepl
        "x" -> callCommand "cowsay I sure hope that fixes it!"
        _ -> callCommand "cowsay learn 2 read son" >> doRepl

msg :: String -> IO ()
msg s = do
  putStrLn (" ========== [ " ++ s ++ " ] ========== ")

srfProgram :: Program -> IO ()
srfProgram p = do
  msg "program"
  print p
  putStrLn ""

srfArity :: Program -> IO ()
srfArity p = do
  msg "arity map"
  print $ collectArity p
  putStrLn ""

-- srfExplicitTypes :: Program -> IO ()
-- srfExplicitTypes p = do
--   msg "explicit type variables"
--   let a = collectArity p
--   print $ explicitTypes a p
--   putStrLn ""

srfConstraints :: Program -> IO ()
srfConstraints p = do
  let (constraints, newProgram) = constrain p
  msg "rewritten program"
  print newProgram
  putStrLn ""
  msg "constraint system"
  showConstraints constraints
  putStrLn ""

-- srfUnify :: Program -> IO ()
-- srfUnify p = do
--   let p' = explicitTypes (collectArity p) p
--   let (constraints, newProgram) = constrain p'
--   msg "unification map:"
--   print . unify . preprocessVariables $ constraints
--   putStrLn ""
