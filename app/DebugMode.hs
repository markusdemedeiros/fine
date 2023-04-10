{-# LANGUAGE FlexibleInstances #-}

module DebugMode where

import BasicChecker (Constraint, FnName, Program, templateProgram, tyckProgram, tyckProgramImp)
import Control.Lens ((^.))
import HindleyMilner (Subst, UnifConstraint, collectArity, constrain, preprocessVariables, rewriteTerms, showConstraints, unify)
import Imp (clone, toImp)
import qualified Imp as I
import Refinements (SubC (..))
import Solve (magic)
import System.Process
import Util (Table, bToList, dom, getDom, getRng, getTbl, todo)

data DebugState = DebugState
  { _working :: Program,
    _constraints :: Table FnName [UnifConstraint],
    _subst :: Subst,
    _impcs :: Table FnName [SubC],
    _imp :: I.Program,
    _vcs :: Table FnName Constraint
  }

class Debuggable x where
  debugStart :: x -> DebugState
  debugMode :: x -> IO ()
  debugMode = doDebugRepl . debugStart

instance Debuggable Program where
  debugStart p = DebugState p (error "HM constraints not generated") (error "subst not generated") (error "impcs not generated") (error "imp program not generated") (error "my brother in christ please generate your VC's before solving them")

instance Debuggable I.Program where
  debugStart p = DebugState (error "no working program") (error "HM constraints not generated") (error "subst not generated") (error "impcs not generated") p (error "my brother in christ please generate your VC's before solving them")

instance Debuggable (Table FnName [SubC]) where
  debugStart impcs = DebugState (error "no working program") (error "HM constraints not generated") (error "subst not generated") impcs (error "imp program not generated") (error "my brother in christ please generate your VC's before solving them")

doDebugRepl :: DebugState -> IO ()
doDebugRepl state = do
  callCommand "cowsay what did you break this time"
  srfProgram state >>= doRepl
  return ()
  where
    doRepl :: DebugState -> IO DebugState
    doRepl s = do
      msg "options"
      putStrLn " - (w)orking program"
      putStrLn " - function a(r)ities"
      putStrLn " - (c)onstraints                          (Hindley Milner)"
      putStrLn " - (u)nification                          (Hindley Milner)"
      putStrLn " - (a)pply subst                          (Hindley Milner)"
      putStrLn " - (t)emplate holes                       (Refinement Inference)"
      putStrLn " - (b)idirectional check imp constraints  (Refinement Inference)"
      putStrLn " - (l)inerize imp constraints             (Refinement Inference)"
      putStrLn " - to (i)mp program                       (Refinement Inference)"
      putStrLn " - (g)enerate VC's                        (Refinement Checking)"
      putStrLn " - (v)erify VC's                          (Refinement Checking)"
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
        "t" -> srfTemplate s >>= doRepl
        "b" -> srfToImp s >>= doRepl
        "l" -> srfLinearlize s >>= doRepl
        "i" -> srfToImpProgram s >>= doRepl
        "g" -> srfCheck s >>= doRepl
        "v" -> srfVerify s >>= doRepl
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

srfTemplate :: DebugState -> IO DebugState
srfTemplate p = do
  let newProgram = templateProgram (_working p)
  msg "templated program"
  print newProgram
  putStrLn ""
  return p {_working = newProgram}

srfToImp :: DebugState -> IO DebugState
srfToImp p = do
  let impcs = tyckProgramImp (_working p)
  msg "imp constraints"
  mapM_ (\x -> putStrLn ("-- " ++ x ++ ":") >> (mapM_ print . getTbl impcs $ x)) (impcs ^. dom)
  putStrLn ""
  return p {_impcs = impcs}

srfLinearlize :: DebugState -> IO DebugState
srfLinearlize p = do
  let impcs = fmap (fmap (\(x, y, z) -> SubC x y z) . clone . fmap (\(SubC x y z) -> (x, y, z))) (_impcs p)
  msg "read-write-once imp constraints"
  mapM_ (\x -> putStrLn ("-- " ++ x ++ ":") >> (mapM_ print . getTbl impcs $ x)) (impcs ^. dom)
  putStrLn ""
  return p {_impcs = impcs}

srfToImpProgram :: DebugState -> IO DebugState
srfToImpProgram p = do
  let impp = toImp (fmap (\(SubC x y z) -> (x, y, z)) . concat . bToList . getRng . _impcs $ p)
  msg "imp program"
  print impp
  putStrLn ""
  return p {_imp = impp}

srfCheck :: DebugState -> IO DebugState
srfCheck p = do
  let vcs = tyckProgram (_working p)
  msg "refinement constraints"
  mapM_ (\x -> putStrLn ("-- " ++ x ++ ":") >> (print . getTbl vcs $ x)) (vcs ^. dom)
  putStrLn ""
  return p {_vcs = vcs}

srfVerify :: DebugState -> IO DebugState
srfVerify p = do
  let vctable = _vcs p
  mapM_
    ( \fn -> do
        putStrLn $ "attempting to verify " ++ fn
        magic (getTbl vctable fn)
    )
    (getDom vctable)
  putStrLn "All bodies complete"
  return p

-- msg "refinement constraints"
-- mapM_ (\x -> putStrLn ("-- " ++ x ++ ":") >> (mapM_ print . getTbl impcs $ x)) (impcs ^. dom)
-- putStrLn ""
-- return p {_impcs = impcs}
