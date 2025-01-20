{-# LANGUAGE OverloadedLists #-}

module Main where

import Test.HUnit
import AU

-- Test cases
tests :: Test
tests = TestList [
    TestLabel "pre-process-1" $ TestCase $
      let (t, subst) = preProcess [Cons (Sym "5") (Sym "5")]
      in assertEqual "Simple pre-process"
         ([Cons (Sym "5") (Sym "5")], [])
         (t, subst)

  , TestLabel "pre-process-2" $ TestCase $
      let (t, _) = preProcess [Cons (Var "x") (Sym "5")]
      in assertEqual "Pre-process with variable"
         [Cons (Sym "c_0") (Sym "5")]
         t

  , TestLabel "pre-process-3" $ TestCase $
      let x = Var "x"
          y = Var "y"
          input = [Cons x (Cons (Sym "5") (Cons y (Cons x y)))]
          (t, _) = preProcess input
      in assertEqual "Complex pre-process"
         [Cons (Sym "c_0") (Cons (Sym "5") (Cons (Sym "c_1") (Cons (Sym "c_0") (Sym "c_1"))))]
         t

  , TestLabel "post-process-1" $ TestCase $
      let x = Var "x"
          y = Var "y"
          input = [Cons x (Cons (Sym "5") (Cons y (Cons x y)))]
          (_, subst) = preProcess input
          invSubst = invertSubst subst
          processed = Cons (Sym "c_0") (Cons (Sym "5") (Cons (Sym "c_1") (Cons (Sym "c_0") (Sym "c_1"))))
      in assertEqual "Post-process"
         input
         [postProcess processed invSubst]

  , TestLabel "au-1" $ TestCase $
      let input = [Sym "5" , Sym "5"]
      in assertEqual "Simple anti-unification"
         (Sym "5")
         (au input)

  , TestLabel "au-2" $ TestCase $
      let input = [Sym "5" , Sym "6"]
      in assertEqual "Different constants"
         (Var "z_0")
         (au input)

  , TestLabel "au-3" $ TestCase $
      let input = [Sym "5", Sym "6", Sym "7"]
      in assertEqual "Three different constants"
         (Var "z_0")
         (au input)

  , TestLabel "au-4" $ TestCase $
      let x = Var "x"
          y = Var "y"
          t1 = Cons (Sym "c") (Cons x (Cons (Sym "c") x))
          t2 = Cons (Sym "d") (Cons x (Cons (Sym "d") y))
          z0 = Var "z_0"
          z1 = Var "z_1"
          expected = Cons z0 (Cons x (Cons z0 z1))
      in assertEqual "Complex anti-unification"
         expected
         (au [t1, t2])

  , TestLabel "au-4b" $ TestCase $
      let x = Var "x"
          y = Var "y"
          t1 = Cons (Sym "c") (Cons y (Cons (Sym "c") x))
          t2 = Cons (Sym "d") (Cons x (Cons (Sym "d") y))
          z0 = Var "z_0"
          z1 = Var "z_1"
          z2 = Var "z_2"
          expected = Cons z0 (Cons z1 (Cons z0 z2))
      in assertEqual "Complex anti-unification with different variables"
         expected
         (au [t1, t2])

  , TestLabel "au-5" $ TestCase $
      let x = Var "x"
          y = Var "y"
          t1 = Cons (Sym "c") (Cons x (Cons (Sym "c") x))
          t2 = Cons (Sym "d") (Cons x (Cons (Sym "d") y))
          t3 = Cons (Sym "d") (Cons x (Cons (Sym "d") y))
          z0 = Var "z_0"
          z1 = Var "z_1"
          expected = Cons z0 (Cons x (Cons z0 z1))
      in assertEqual "Three terms anti-unification"
         expected
         (au [t1, t2, t3])

  , TestLabel "au-6" $ TestCase $
      let t1 = Cons (Sym "lambda") (Cons (Sym "5") (Sym "5"))
          t2 = Cons (Sym "lambda") (Cons (Sym "t") (Sym "t"))
          z0 = Var "z_0"
          expected = Cons (Sym "lambda") (Cons z0 z0)
      in assertEqual "Lambda abstraction"
         expected
         (au [t1, t2])

  , TestLabel "au-7" $ TestCase $
      let t1 = Cons (Sym "lambda") (Cons (Sym "5") (Sym "5"))
          t2 = Cons (Sym "lambda") (Cons (Sym "t") (Sym "t"))
          t3 = Cons (Sym "lambda") (Cons (Sym "5") (Sym "6"))
          z0 = Var "z_0"
          z1 = Var "z_1"
          expected = Cons (Sym "lambda") (Cons z0 z1)
      in assertEqual "Lambda abstraction with three terms"
         expected
         (au [t1, t2, t3])

  , TestLabel "au-8" $ TestCase $
      let t1 = Cons (Sym "lambda") (Cons (Sym "5") (Sym "5"))
          t2 = Cons (Sym "lambda") (Cons (Sym "t") (Sym "t"))
          x = Var "x"
          t_lhs = Cons (Sym "lambda") (Cons x x)
          t_rhs = au [t1, t2]
          z0 = Var "z_0"
          expected = Cons (Sym "lambda") (Cons z0 z0)
      in assertEqual "Lambda abstraction comparison"
         expected
         (au [t_lhs, t_rhs])

  , TestLabel "au-9" $ TestCase $
      let t1 = Cons (Sym "lambda") (Cons (Sym "5") (Sym "5"))
          t2 = Cons (Sym "lambda") (Cons (Sym "t") (Sym "t"))
          t3 = Cons (Sym "lambda") (Cons (Sym "5") (Sym "6"))
          x = Var "x"
          t_lhs = Cons (Sym "lambda") (Cons x x)
          t_rhs = au [t1, t2, t3]
          z0 = Var "z_0"
          z1 = Var "z_1"
          expected = Cons (Sym "lambda") (Cons z0 z1)
      in assertEqual "Lambda abstraction comparison with three terms"
         expected
         (au [t_lhs, t_rhs])

  , TestLabel "au-10" $ TestCase $
      let x = Var "x"
          y = Var "y"
          t1 = Cons (Sym "lambda") (Cons x x)
          t2 = Cons (Sym "lambda") (Cons y y)
          z0 = Var "z_0"
          expected = Cons (Sym "lambda") (Cons z0 z0)
      in assertEqual "Lambda abstraction with different variables"
         expected
         (au [t1, t2])

  , TestLabel "au-11" $ TestCase $
      let x = Var "x"
          t1 = Cons (Sym "lambda") (Cons x x)
          t2 = Cons (Sym "lambda") (Cons x x)
          expected = Cons (Sym "lambda") (Cons x x)
      in assertEqual "Lambda abstraction with same variable"
         expected
         (au [t1, t2])
  ]

-- Run all tests
main :: IO Counts
main = runTestTT tests