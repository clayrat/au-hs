{-# LANGUAGE OverloadedLists #-}

module Main where

import Test.HUnit

import Term
import Subst
import Unify
import AU

-- Test cases
tests :: Test
tests = TestList [
    TestLabel "pre-process-1" $ TestCase $
      let (t, subst) = preProcess [Cons (sym "5") (sym "5")]
      in assertEqual "Simple pre-process"
         ([Cons (sym "5") (sym "5")], [])
         (t, subst)

  , TestLabel "pre-process-2" $ TestCase $
      let (t, _) = preProcess [Cons (var "x") (sym "5")]
      in assertEqual "Pre-process with variable"
         [Cons (sym "c_0") (sym "5")]
         t

  , TestLabel "pre-process-3" $ TestCase $
      let x = var "x"
          y = var "y"
          input = [Cons x (Cons (sym "5") (Cons y (Cons x y)))]
          (t, _) = preProcess input
      in assertEqual "Complex pre-process"
         [Cons (sym "c_0") (Cons (sym "5") (Cons (sym "c_1") (Cons (sym "c_0") (sym "c_1"))))]
         t

  , TestLabel "post-process-1" $ TestCase $
      let x = var "x"
          y = var "y"
          input = [Cons x (Cons (sym "5") (Cons y (Cons x y)))]
          (_, subst) = preProcess input
          invSubst = invertSubst subst
          processed = Cons (sym "c_0") (Cons (sym "5") (Cons (sym "c_1") (Cons (sym "c_0") (sym "c_1"))))
      in assertEqual "Post-process"
         input
         [postProcess processed invSubst]

  , TestLabel "au-1" $ TestCase $
      let input = [sym "5" , sym "5"]
      in assertEqual "Simple anti-unification"
         (sym "5")
         (au input)

  , TestLabel "au-2" $ TestCase $
      let input = [sym "5" , sym "6"]
      in assertEqual "Different constants"
         (var "z_0")
         (au input)

  , TestLabel "au-3" $ TestCase $
      let input = [sym "5", sym "6", sym "7"]
      in assertEqual "Three different constants"
         (var "z_0")
         (au input)

  , TestLabel "au-4" $ TestCase $
      let x = var "x"
          c = sym "c"
          d = sym "d"
          z0 = var "z_0"
          t1 =       Cons c  (Cons x (Cons c   x         ))
          t2 =       Cons d  (Cons x (Cons d  (var "y")  ))
          expected = Cons z0 (Cons x (Cons z0 (var "z_1")))
      in assertEqual "Complex anti-unification"
         expected
         (au [t1, t2])

  , TestLabel "au-4b" $ TestCase $
      let x = var "x"
          y = var "y"
          z0 = var "z_0"
          z1 = var "z_1"
          z2 = var "z_2"
          t1 =       Cons (sym "c") (Cons y  (Cons (sym "c") x ))
          t2 =       Cons (sym "d") (Cons x  (Cons (sym "d") y ))
          expected = Cons  z0       (Cons z1 (Cons  z0       z2))
      in assertEqual "Complex anti-unification with different variables"
         expected
         (au [t1, t2])

  , TestLabel "au-5" $ TestCase $
      let x = var "x"
          y = var "y"
          z0 = var "z_0"
          z1 = var "z_1"
          t1 = Cons (sym "c") (Cons x (Cons (sym "c") x))
          t2 = Cons (sym "d") (Cons x (Cons (sym "d") y))
          t3 = Cons (sym "d") (Cons x (Cons (sym "d") y))
          expected = Cons z0 (Cons x (Cons z0 z1))
      in assertEqual "Three terms anti-unification"
         expected
         (au [t1, t2, t3])

  , TestLabel "au-6" $ TestCase $
      let z0 = var "z_0"
          t1 =       Cons (sym "lambda") (Cons (sym "5") (sym "5"))
          t2 =       Cons (sym "lambda") (Cons (sym "t") (sym "t"))
          expected = Cons (sym "lambda") (Cons  z0        z0      )
      in assertEqual "Lambda abstraction"
         expected
         (au [t1, t2])

  , TestLabel "au-7" $ TestCase $
      let z0 = var "z_0"
          z1 = var "z_1"
          t1 =       Cons (sym "lambda") (Cons (sym "5") (sym "5"))
          t2 =       Cons (sym "lambda") (Cons (sym "t") (sym "t"))
          t3 =       Cons (sym "lambda") (Cons (sym "5") (sym "6"))
          expected = Cons (sym "lambda") (Cons  z0        z1      )
      in assertEqual "Lambda abstraction with three terms"
         expected
         (au [t1, t2, t3])

  , TestLabel "au-8" $ TestCase $
      let x = var "x"
          z0 = var "z_0"
          t1 =       Cons (sym "lambda") (Cons (sym "5") (sym "5"))
          t2 =       Cons (sym "lambda") (Cons (sym "t") (sym "t"))
          t_lhs =    Cons (sym "lambda") (Cons  x         x       )
          t_rhs = au [t1, t2]
          expected = Cons (sym "lambda") (Cons  z0        z0      )
      in assertEqual "Lambda abstraction comparison"
         expected
         (au [t_lhs, t_rhs])

  , TestLabel "au-9" $ TestCase $
      let x = var "x"
          z0 = var "z_0"
          z1 = var "z_1"
          t1 =       Cons (sym "lambda") (Cons (sym "5") (sym "5"))
          t2 =       Cons (sym "lambda") (Cons (sym "t") (sym "t"))
          t3 =       Cons (sym "lambda") (Cons (sym "5") (sym "6"))
          t_lhs =    Cons (sym "lambda") (Cons  x         x       )
          t_rhs = au [t1, t2, t3]
          expected = Cons (sym "lambda") (Cons  z0        z1      )
      in assertEqual "Lambda abstraction comparison with three terms"
         expected
         (au [t_lhs, t_rhs])

  , TestLabel "au-10" $ TestCase $
      let x = var "x"
          y = var "y"
          z0 = var "z_0"
          t1 =       Cons (sym "lambda") (Cons x  x )
          t2 =       Cons (sym "lambda") (Cons y  y )
          expected = Cons (sym "lambda") (Cons z0 z0)
      in assertEqual "Lambda abstraction with different variables"
         expected
         (au [t1, t2])

  , TestLabel "au-11" $ TestCase $
      let x = var "x"
          t1 =       Cons (sym "lambda") (Cons x x)
          t2 =       Cons (sym "lambda") (Cons x x)
          expected = Cons (sym "lambda") (Cons x x)
      in assertEqual "Lambda abstraction with same variable"
         expected
         (au [t1, t2])

  , TestLabel "unify-1" $ TestCase $
      let t1 = Cons (sym "a") (sym "b")
          t2 = Cons (sym "a") (sym "b")
          expected = Left []
      in assertEqual "Unify identical terms"
         expected
         (unify [(t1, t2)])

  , TestLabel "unify-2" $ TestCase $
      let t1 = Cons (var "x") (sym "b")
          t2 = Cons (sym "a") (sym "b")
          expected = Left [(Id "x", sym "a")]
      in assertEqual "Unify with variable"
         expected
         (unify [(t1, t2)])

  , TestLabel "unify-3" $ TestCase $
      let t1 = Cons (var "x") (var "y")
          t2 = Cons (sym "a") (sym "b")
          expected = Left [(Id "x", sym "a"), (Id "y", sym "b")]
      in assertEqual "Unify with two variables"
         expected
         (unify [(t1, t2)])

  , TestLabel "unify-4" $ TestCase $
      let t1 = Cons (var "x") (var "x")
          t2 = Cons (sym "a") (sym "b")
          expected = Right (ArrArrRec (SubsRecL (ConCon (Sy "a") (Sy "b"))))
      in assertEqual "Unify with conflicting variables"
         expected
         (unify [(t1, t2)])

  , TestLabel "unify-5" $ TestCase $
      let t1 = Cons (var "x") (Cons (var "y") (var "x"))
          t2 = Cons (sym "a") (Cons (sym "b") (sym "a"))
          expected = Left [(Id "x", sym "a"), (Id "y", sym "b")]
      in assertEqual "Unify nested terms"
         expected
         (unify [(t1, t2)])
  ]

-- Run all tests
main :: IO Counts
main = runTestTT tests