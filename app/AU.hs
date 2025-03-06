module AU where

import Control.Monad.State
import Data.Char (ord, chr)
import Term
import Subst

gen :: Char -> (String -> b) -> a -> State (Int, Subst a b) b
gen c f a = do
  (n, s) <- get
  let b = f (c : '_' : [chr (ord '0' + n)])
  put (n + 1, (a, b) : s)
  return b

preProcess :: [Term] -> ([Term], Subst Id Sy)
preProcess terms =
  let (t, (_ , s)) = runState (mapM preProcess' terms) (0, [])
  in (t , s)
  where
    preProcess' :: Term -> State (Int, Subst Id Sy) Term
    preProcess' (Arr a d) =
      do a' <- preProcess' a
         d' <- preProcess' d
         pure (Arr a' d')
    preProcess' (Var v) =
      do sub <- gets snd
         case lookupSubst v sub of
           Just c -> pure (Sym c)
           Nothing ->
             do c <- gen 'c' Sy v
                pure (Sym c)
    preProcess' t = pure t

auTheta :: [Term] -> State (Int, Subst [Term] Id) Term
auTheta terms =
  if null terms
    then error "auTheta: |terms| must be > 0"
    else do theta <- gets snd
            case terms of
              (t:ts) | all (== t) ts ->  -- Rule 7
                pure t
              ts | all isArr ts ->  -- Rule 8
                do s  <- auTheta [t1 | Arr t1 _ <- ts]
                   s' <- auTheta [t2 | Arr _ t2 <- ts]
                   pure (Arr s s')
              ts ->
                case lookupSubst ts theta of
                  Just x -> pure (Var x) -- Rule 9
                  Nothing ->  -- Rule 10
                    do z <- gen 'z' Id terms
                       pure (Var z)

postProcess :: Term -> Subst Sy Id -> Term
postProcess   (Arr a d) sub = Arr (postProcess a sub) (postProcess d sub)
postProcess c@(Sym s)   sub = maybe c Var (lookupSubst s sub)
postProcess t           _   = t

-- Anti-unification
au :: [Term] -> Term
au terms =
  if null terms
    then error "au: |terms| must be > 0"
    else let (terms', sub) = preProcess terms
             invSubst = invertSubst sub
             s = evalState (auTheta terms') (0, [])  -- Rule 6
         in postProcess s invSubst
