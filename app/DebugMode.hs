module DebugMode where

import BasicChecker (FnName, Program)
import HindleyMilner (Subst, UnifConstraint, collectArity, constrain, preprocessVariables, rewriteTerms, showConstraints, unify)
import System.Process
import Util (Table, bToList, getRng, todo)

data DebugState = DebugState {_working :: Program, _constraints :: Table FnName [UnifConstraint], _subst :: Subst, _imp :: Program}

debugMode :: Program -> IO ()
debugMode p = do
  callCommand "cowsay what did you break this time"
  let state = DebugState p (error "HM constraints not generated") (error "subst not generated") (error "imp program not generated")
  srfProgram state >>= doRepl
  return ()
  where
    doRepl :: DebugState -> IO DebugState
    doRepl s = do
      msg "options"
      putStrLn " - (w)orking program"
      putStrLn " - function a(r)ities"
      putStrLn " - (c)onstraints (Hindley Milner)"
      putStrLn " - (u)nification (Hindley Milner)"
      putStrLn " - (a)pply subst (Hindley Milner)"
      putStrLn " - e(x)it"
      putStr "> "
      cmd <- getLine
      putStrLn ""
      case cmd of
        "w" -> srfProgram s >>= doRepl
        "r" -> srfArity s >>= doRepl
        "c" -> srfConstraints s >>= doRepl
        "u" -> srfUnify s >>= doRepl
        "a" -> srfApplySubst s >>= doRepl
        "x" -> callCommand "cowsay I sure hope that fixes it!" >> return s
        _ -> callCommand "cowsay learn 2 read son" >> doRepl s

msg :: String -> IO ()
msg s = do
  putStrLn (" ========== [ " ++ s ++ " ] ========== ")

srfProgram :: DebugState -> IO DebugState
srfProgram p = do
  msg "program"
  print (_working p)
  putStrLn ""
  return p

srfArity :: DebugState -> IO DebugState
srfArity p = do
  msg "arity map"
  print $ collectArity (_working p)
  putStrLn ""
  return p

-- srfExplicitTypes :: Program -> IO ()
-- srfExplicitTypes p = do
--   msg "explicit type variables"
--   let a = collectArity p
--   print $ explicitTypes a p
--   putStrLn ""

srfConstraints :: DebugState -> IO DebugState
srfConstraints p = do
  let (constraints, newProgram) = constrain (_working p)
  msg "rewritten program"
  print newProgram
  putStrLn ""
  msg "constraint system"
  showConstraints constraints
  putStrLn ""
  return $ p {_working = newProgram, _constraints = constraints}

srfUnify :: DebugState -> IO DebugState
srfUnify p = do
  msg "unification map:"
  let u = unify . preprocessVariables . concat . bToList . getRng . _constraints $ p
  print u
  putStrLn ""
  return p {_subst = u}

srfApplySubst :: DebugState -> IO DebugState
srfApplySubst p = do
  let newProgram = rewriteTerms (_subst p) (_working p)
  msg "rewritten program"
  print newProgram
  putStrLn ""
  return p {_working = newProgram}
