module DebugMode where

import BasicChecker (Program)
import HindleyMilner (constrain, preprocessVariables, showConstraints, unify)
import System.Process
import Util (todo)

debugMode :: Program -> IO ()
debugMode p = do
  callCommand "cowsay I wonder what stupid thing you did this time"
  msg "program"
  print p
  doRepl
  where
    doRepl = do
      msg "options"
      putStrLn " - (i)nput program"
      putStrLn " - (c)onstraints (HM)"
      putStrLn " - (u)nification (HM)"
      putStrLn " - e(x)it"
      putStr "> "
      cmd <- getLine
      putStrLn ""
      case cmd of
        "i" -> print p >> doRepl
        "c" -> srfConstraints p >> doRepl
        "u" -> srfUnify p >> doRepl
        "x" -> callCommand "cowsay I sure hope that fixes it!"
        _ -> callCommand "cowsay learn 2 read son" >> doRepl

msg :: String -> IO ()
msg s = do
  putStrLn ""
  putStrLn (" ========== [ " ++ s ++ " ] ========== ")

srfConstraints :: Program -> IO ()
srfConstraints p = do
  let newProgram = snd $ constrain p
  putStrLn "[LOG fine] rewritten program:"
  print newProgram
  putStrLn ""
  putStrLn "[LOG fine] constraint system:"
  showConstraints p
  putStrLn ""

srfUnify :: Program -> IO ()
srfUnify p = do
  let (constraints, newProgram) = constrain p
  putStrLn "[LOG fine] unification map:"
  print . unify . preprocessVariables $ constraints
  putStrLn ""
