{-# LANGUAGE OverloadedLists #-}

module Main where

import Test.HUnit
import AU

-- Helper function to create nested lists into Term structure
toTerm :: [Either String Term] -> Term
toTerm [] = error "Empty list"
toTerm [Left s] = Symbol s
toTerm [Right t] = t
toTerm (x:xs) = Cons (either Symbol id x) (toTerm xs)

-- Test cases
tests :: Test
tests = TestList [
    TestLabel "pre-process-1" $ TestCase $
      let (t, subst) = preProcess [toTerm [Left "5", Left "5"]]
      in assertEqual "Simple pre-process"
         ([toTerm [Left "5", Left "5"]], [])
         (t, subst)

  , TestLabel "pre-process-2" $ TestCase $
      let (t, _) = preProcess [toTerm [Right (Var "x"), Left "5"]]
      in assertEqual "Pre-process with variable"
         [toTerm [Left "c_0", Left "5"]]
         t

  , TestLabel "pre-process-3" $ TestCase $
      let x = Var "x"
          y = Var "y"
          input = [toTerm [Right x, Left "5", Right y, Right (toTerm [Right x, Right y])]]
          (t, _) = preProcess input
      in assertEqual "Complex pre-process"
         [toTerm [Left "c_0", Left "5", Left "c_1", Right (toTerm [Left "c_0", Left "c_1"])]]
         t

  , TestLabel "post-process-1" $ TestCase $
      let x = Var "x"
          y = Var "y"
          input = [toTerm [Right x, Left "5", Right y, Right (toTerm [Right x, Right y])]]
          (_, subst) = preProcess input
          invSubst = invertSubst subst
          processed = toTerm [Left "c_0", Left "5", Left "c_1", Right (toTerm [Left "c_0", Left "c_1"])]
      in assertEqual "Post-process"
         input
         [postProcess processed invSubst]

  , TestLabel "au-1" $ TestCase $
      let input = [toTerm [Left "5", Left "5"]]
      in assertEqual "Simple anti-unification"
         (toTerm [Left "5", Left "5"])
         (au input)

  , TestLabel "au-2" $ TestCase $
      let input = [toTerm [Left "5"], toTerm [Left "6"]]
      in assertEqual "Different constants"
         (Var "z_0")
         (au input)

  , TestLabel "au-3" $ TestCase $
      let input = [toTerm [Left "5"], toTerm [Left "6"], toTerm [Left "7"]]
      in assertEqual "Three different constants"
         (Var "z_0")
         (au input)

  , TestLabel "au-4" $ TestCase $
      let x = Var "x"
          y = Var "y"
          t1 = toTerm [Left "c", Right x, Right (toTerm [Left "c", Right x])]
          t2 = toTerm [Left "d", Right x, Right (toTerm [Left "d", Right y])]
          z0 = Var "z_0"
          z1 = Var "z_1"
          expected = toTerm [Right z0, Right x, Right (toTerm [Right z0, Right z1])]
      in assertEqual "Complex anti-unification"
         expected
         (au [t1, t2])

  , TestLabel "au-4b" $ TestCase $
      let x = Var "x"
          y = Var "y"
          t1 = toTerm [Left "c", Right y, Right (toTerm [Left "c", Right x])]
          t2 = toTerm [Left "d", Right x, Right (toTerm [Left "d", Right y])]
          z0 = Var "z_0"
          z1 = Var "z_1"
          z2 = Var "z_2"
          expected = toTerm [Right z0, Right z1, Right (toTerm [Right z0, Right z2])]
      in assertEqual "Complex anti-unification with different variables"
         expected
         (au [t1, t2])

  , TestLabel "au-5" $ TestCase $
      let x = Var "x"
          y = Var "y"
          t1 = toTerm [Left "c", Right x, Right (toTerm [Left "c", Right x])]
          t2 = toTerm [Left "d", Right x, Right (toTerm [Left "d", Right y])]
          t3 = toTerm [Left "d", Right x, Right (toTerm [Left "d", Right y])]
          z0 = Var "z_0"
          z1 = Var "z_1"
          expected = toTerm [Right z0, Right x, Right (toTerm [Right z0, Right z1])]
      in assertEqual "Three terms anti-unification"
         expected
         (au [t1, t2, t3])

  , TestLabel "au-6" $ TestCase $
      let t1 = toTerm [Left "lambda", Right (toTerm [Left "5"]), Left "5"]
          t2 = toTerm [Left "lambda", Right (toTerm [Left "#t"]), Left "#t"]
          z0 = Var "z_0"
          expected = toTerm [Left "lambda", Right (toTerm [Right z0]), Right z0]
      in assertEqual "Lambda abstraction"
         expected
         (au [t1, t2])

  , TestLabel "au-7" $ TestCase $
      let t1 = toTerm [Left "lambda", Right (toTerm [Left "5"]), Left "5"]
          t2 = toTerm [Left "lambda", Right (toTerm [Left "#t"]), Left "#t"]
          t3 = toTerm [Left "lambda", Right (toTerm [Left "5"]), Left "6"]
          z0 = Var "z_0"
          z1 = Var "z_1"
          expected = toTerm [Left "lambda", Right (toTerm [Right z0]), Right z1]
      in assertEqual "Lambda abstraction with three terms"
         expected
         (au [t1, t2, t3])

  , TestLabel "au-8" $ TestCase $
      let t1 = toTerm [Left "lambda", Right (toTerm [Left "5"]), Left "5"]
          t2 = toTerm [Left "lambda", Right (toTerm [Left "#t"]), Left "#t"]
          x = Var "x"
          t_lhs = toTerm [Left "lambda", Right (toTerm [Right x]), Right x]
          t_rhs = au [t1, t2]
          z0 = Var "z_0"
          expected = toTerm [Left "lambda", Right (toTerm [Right z0]), Right z0]
      in assertEqual "Lambda abstraction comparison"
         expected
         (au [t_lhs, t_rhs])

  , TestLabel "au-9" $ TestCase $
      let t1 = toTerm [Left "lambda", Right (toTerm [Left "5"]), Left "5"]
          t2 = toTerm [Left "lambda", Right (toTerm [Left "#t"]), Left "#t"]
          t3 = toTerm [Left "lambda", Right (toTerm [Left "5"]), Left "6"]
          x = Var "x"
          t_lhs = toTerm [Left "lambda", Right (toTerm [Right x]), Right x]
          t_rhs = au [t1, t2, t3]
          z0 = Var "z_0"
          z1 = Var "z_1"
          expected = toTerm [Left "lambda", Right (toTerm [Right z0]), Right z1]
      in assertEqual "Lambda abstraction comparison with three terms"
         expected
         (au [t_lhs, t_rhs])

  , TestLabel "au-10" $ TestCase $
      let x = Var "x"
          y = Var "y"
          t1 = toTerm [Left "lambda", Right (toTerm [Right x]), Right x]
          t2 = toTerm [Left "lambda", Right (toTerm [Right y]), Right y]
          z0 = Var "z_0"
          expected = toTerm [Left "lambda", Right (toTerm [Right z0]), Right z0]
      in assertEqual "Lambda abstraction with different variables"
         expected
         (au [t1, t2])

  , TestLabel "au-11" $ TestCase $
      let x = Var "x"
          t1 = toTerm [Left "lambda", Right (toTerm [Right x]), Right x]
          t2 = toTerm [Left "lambda", Right (toTerm [Right x]), Right x]
          expected = toTerm [Left "lambda", Right (toTerm [Right x]), Right x]
      in assertEqual "Lambda abstraction with same variable"
         expected
         (au [t1, t2])
  ]

-- Run all tests
main :: IO Counts
main = runTestTT tests