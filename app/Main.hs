{-# LANGUAGE OverloadedLists #-}

module Main where

import Test.HUnit

import Base
import Term
import Subst
import Unify
import AU

-- Test cases
tests :: Test
tests = TestList [
    TestLabel "pre-process-1" $ TestCase $
      let (t, subst) = preProcess [Arr (sym "c") (sym "c")]
      in assertEqual "Simple pre-process"
         ([Arr (sym "c") (sym "c")], [])
         (t, subst)

  , TestLabel "pre-process-2" $ TestCase $
      let (t, _) = preProcess [Arr (var "x") (sym "c")]
      in assertEqual "Pre-process with variable"
         [Arr (sym "c'") (sym "c")]
         t

  , TestLabel "pre-process-3" $ TestCase $
      let x = var "x"
          y = var "y"
          input = [Arr x (Arr (sym "c") (Arr y (Arr x y)))]
          (t, _) = preProcess input
      in assertEqual "Complex pre-process"
         [Arr (sym "c'") (Arr (sym "c") (Arr (sym "c''") (Arr (sym "c'") (sym "c''"))))]
         t

  , TestLabel "post-process-1" $ TestCase $
      let x = var "x"
          y = var "y"
          input = [Arr x (Arr (sym "c") (Arr y (Arr x y)))]
          (_, subst) = preProcess input
          invSubst = invertSubst subst
          processed = Arr (sym "c'") (Arr (sym "c") (Arr (sym "c''") (Arr (sym "c'") (sym "c''"))))
      in assertEqual "Post-process"
         input
         [postProcess processed invSubst]

  , TestLabel "au-1" $ TestCase $
      let input = [sym "c" , sym "c"]
      in assertEqual "Simple anti-unification"
         (sym "c")
         (au input)

  , TestLabel "au-2" $ TestCase $
      let input = [sym "c" , sym "d"]
      in assertEqual "Different constants"
         (var "z")
         (au input)

  , TestLabel "au-3" $ TestCase $
      let input = [sym "c", sym "d", sym "e"]
      in assertEqual "Three different constants"
         (var "z")
         (au input)

  , TestLabel "au-4" $ TestCase $
      let x = var "x"
          c = sym "c"
          d = sym "d"
          y' = var "y'"
          t1 =       Arr c  (Arr x (Arr c   x         ))
          t2 =       Arr d  (Arr x (Arr d  (var "y")  ))
          expected = Arr y' (Arr x (Arr y' (var "y''")))
      in assertEqual "Complex anti-unification"
         expected
         (au [t1, t2])

  , TestLabel "au-4b" $ TestCase $
      let x = var "x"
          y = var "y"
          y' = var "y'"
          t1 =       Arr (sym "c") (Arr y           (Arr (sym "c")  x          ))
          t2 =       Arr (sym "d") (Arr x           (Arr (sym "d")  y          ))
          expected = Arr  y'       (Arr (var "y''") (Arr  y'       (var "y'''")))
      in assertEqual "Complex anti-unification with different variables"
         expected
         (au [t1, t2])

  , TestLabel "au-5" $ TestCase $
      let x = var "x"
          y = var "y"
          y' = var "y'"
          t1       = Arr (sym "c") (Arr x (Arr (sym "c")  x         ))
          t2       = Arr (sym "d") (Arr x (Arr (sym "d")  y         ))
          t3       = Arr (sym "d") (Arr x (Arr (sym "d")  y         ))
          expected = Arr  y'       (Arr x (Arr  y'       (var "y''")))
      in assertEqual "Three terms anti-unification"
         expected
         (au [t1, t2, t3])

  , TestLabel "au-6" $ TestCase $
      let z  = var "z"
          t1 =       Arr (sym "lambda") (Arr (sym "c") (sym "c"))
          t2 =       Arr (sym "lambda") (Arr (sym "t") (sym "t"))
          expected = Arr (sym "lambda") (Arr  z         z       )
      in assertEqual "Lambda abstraction"
         expected
         (au [t1, t2])

  , TestLabel "au-7" $ TestCase $
      let t1 =       Arr (sym "lambda") (Arr (sym "c") (sym "c" ))
          t2 =       Arr (sym "lambda") (Arr (sym "t") (sym "t" ))
          t3 =       Arr (sym "lambda") (Arr (sym "c") (sym "d" ))
          expected = Arr (sym "lambda") (Arr (var "z") (var "z'"))
      in assertEqual "Lambda abstraction with three terms"
         expected
         (au [t1, t2, t3])

  , TestLabel "au-8" $ TestCase $
      let x = var "x"
          z' = var "z'"
          t1 =       Arr (sym "lambda") (Arr (sym "c") (sym "c"))
          t2 =       Arr (sym "lambda") (Arr (sym "t") (sym "t"))
          t_lhs =    Arr (sym "lambda") (Arr  x         x       )
          t_rhs = au [t1, t2]
          expected = Arr (sym "lambda") (Arr  z'        z'      )
      in assertEqual "Lambda abstraction comparison"
         expected
         (au [t_lhs, t_rhs])

  , TestLabel "au-9" $ TestCase $
      let x = var "x"
          t1 =       Arr (sym "lambda") (Arr (sym "c")  (sym "c"  ))
          t2 =       Arr (sym "lambda") (Arr (sym "t")  (sym "t"  ))
          t3 =       Arr (sym "lambda") (Arr (sym "c")  (sym "d"  ))
          t_lhs =    Arr (sym "lambda") (Arr  x          x         )
          t_rhs = au [t1, t2, t3]
          expected = Arr (sym "lambda") (Arr (var "z''") (var "z'''"))
      in assertEqual "Lambda abstraction comparison with three terms"
         expected
         (au [t_lhs, t_rhs])

  , TestLabel "au-10" $ TestCase $
      let x = var "x"
          y = var "y"
          y' = var "y'"
          t1 =       Arr (sym "lambda") (Arr x  x )
          t2 =       Arr (sym "lambda") (Arr y  y )
          expected = Arr (sym "lambda") (Arr y' y')
      in assertEqual "Lambda abstraction with different variables"
         expected
         (au [t1, t2])

  , TestLabel "au-11" $ TestCase $
      let x = var "x"
          t1 =       Arr (sym "lambda") (Arr x x)
          t2 =       Arr (sym "lambda") (Arr x x)
          expected = Arr (sym "lambda") (Arr x x)
      in assertEqual "Lambda abstraction with same variable"
         expected
         (au [t1, t2])

  -- Unification tests

  , TestLabel "unify-1" $ TestCase $
      let t1 = Arr (sym "a") (sym "b")
          t2 = Arr (sym "a") (sym "b")
          expected = Left []
      in assertEqual "Unify identical terms"
         expected
         (unify [(t1, t2)])

  , TestLabel "unify-2" $ TestCase $
      let t1 = Arr (var "x") (sym "b")
          t2 = Arr (sym "a") (sym "b")
          expected = Left [(Id "x", sym "a")]
      in assertEqual "Unify with variable"
         expected
         (unify [(t1, t2)])

  , TestLabel "unify-3" $ TestCase $
      let t1 = Arr (var "x") (var "y")
          t2 = Arr (sym "a") (sym "b")
          expected = Left [(Id "x", sym "a"), (Id "y", sym "b")]
      in assertEqual "Unify with two variables"
         expected
         (unify [(t1, t2)])

  , TestLabel "unify-4" $ TestCase $
      let t1 = Arr (var "x") (var "x")
          t2 = Arr (sym "a") (sym "b")
          expected = Right (ArrArrRec (SubsRecL (SymSym (Sy "a") (Sy "b"))))
      in assertEqual "Unify with conflicting variables"
         expected
         (unify [(t1, t2)])

  , TestLabel "unify-5" $ TestCase $
      let t1 = Arr (var "x") (Arr (var "y") (var "x"))
          t2 = Arr (sym "a") (Arr (sym "b") (sym "a"))
          expected = Left [(Id "x", sym "a"), (Id "y", sym "b")]
      in assertEqual "Unify nested terms"
         expected
         (unify [(t1, t2)])
  ]

-- Run all tests
main :: IO Counts
main = runTestTT tests