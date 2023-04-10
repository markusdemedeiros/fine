{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant $" #-}
module Main where

import BasicChecker (Program, binder)
import DebugMode (Debuggable, debugMode)
import HindleyMilner
import qualified Imp as I
import Surface
import Util (todo)

main :: IO ()
main = putStrLn "click https://www.youtube.com/watch?v=dQw4w9WgXcQ to access program (or enter DebugMode from the repl)"

-- | All Srf functions must have a type! But not all types must have a term
debug :: (Debuggable x) => x -> IO ()
debug = debugMode

prog1 :: Program
prog1 = parse $ do
  _val "assert" $ refn "unused" (refine bool (var' binder)) int
  _let "assert" ["b"] $
    integer 0

  _val "not" $ refn "x" bool (refine bool (eq' (var' binder) (neg' (var' "x"))))
  _let "not" ["x"] $
    cond
      "x"
      false
      true

  _val "and" $ refn "x" bool (refn "y" bool (refine bool (eq' (var' binder) (and' (var' "x") (var' "y")))))
  _let "and" ["x", "y"] $
    cond
      "x"
      (var "y")
      false

  _val "or" $ refn "x" bool (refn "y" bool (refine bool (eq' (var' binder) (or' (var' "x") (var' "y")))))
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
  _val "or" $ refn "x" bool (refn "y" bool (refine bool (eq' (var' binder) (or' (var' "x") (var' "y")))))
  _let "or" ["x", "y"] $
    cond
      "x"
      true
      (var "y")

prog3 :: Program
prog3 = parse $ do
  _val "v" $ refine int (eq' (var' binder) (int' 4))
  _let "main" [] $
    app (lam "x" (var "x")) "id"

prog4 :: Program
prog4 = parse $ do
  _val "x" $ refn "unused" (tyv "'a") (tyv "'b")
  _let "x" ["vv"] $ (var "vv")
  _val "y" $ refn "unused" bool int
  -- _val "y" $ fn (tyv "'b") (tyv "'a")
  -- _val "main" $ fn (tyv "'e") (tyv "'f")
  _val "main" $ refn "unused" bool (refn "unused'" bool int)
  _let "main" ["z"] $
    cond "z" (var "x") (var "y")

prog5 :: Program
prog5 = parse $ do
  _val "assert" $ refn "b" (refine bool (var' binder)) int
  -- _let "assert" ["b"] $ integer 0

  _val "zero" $ refine int (eq' (var' binder) (int' 0))

  -- explicit version (no holes)
  _val "abs" $ refn "x" int (refine int (leq' (int' 0) (var' binder)))
  _let "abs" ["x"] $
    bind "c" (app (app leq "zero") "x") $
      cond
        "c"
        (var "x")
        (app (app sub "zero") "x")

  _val "main" $ refn "y" int int
  _let "main" ["y"] $
    bind "z" (app (var "abs") "y") $
      bind "c" (app (app leq "zero") "z") $
        (app (var "assert") "c")

prog6 :: Program
prog6 = parse $ do
  _val "assert" $ refn "b" (refine bool (var' binder)) int
  -- _let "assert" ["b"] $ integer 0

  _val "zero" $ refine int (eq' (var' binder) (int' 0))

  -- explicit version (no holes)
  _val "abs" $ refn "x" int (hole int)
  _let "abs" ["x"] $
    bind "c" (app (app leq "zero") "x") $
      cond
        "c"
        (var "x")
        (app (app sub "zero") "x")

  _val "main" $ refn "y" int int
  _let "main" ["y"] $
    bind "z" (app (var "abs") "y") $
      bind "c" (app (app leq "zero") "z") $
        (app (var "assert") "c")

prog7 :: Program
prog7 = parse $ do
  _val "succ" $ refn "x" int (hole int)
  _let "succ" ["x"] $
    bind "one" (integer 1) $
      app (app add "one") "x"

prog8 :: Program
prog8 = parse $ do
  _val "test" $ refn "unused" (tyv "a") (tyv "a")

  _val "main" $ refn "unused" int int
  _let "main" [] $
    var "test"

-- We're also able to debug Imp programs

imp1 :: I.Program
imp1 = todo