module AU where

import Control.Monad.State

import Base
import Term
import Subst

gen :: Unfinite b => a -> State (b, Subst a b) b
gen a = do
  (x, s) <- get
  put (fresh1 x, (a, x) : s)
  return x

preProcess :: [Term] -> ([Term], Subst Id Sy)
preProcess terms =
  let sys = concatMap syms terms
      (t, (_ , s)) = runState (mapM preProcess' terms) (fresh sys, [])
  in (t , s)
  where
    preProcess' :: Term -> State (Sy, Subst Id Sy) Term
    preProcess' (Arr a d) =
      do a' <- preProcess' a
         d' <- preProcess' d
         pure (Arr a' d')
    preProcess' (Var v) =
      do sub <- gets snd
         case lookupSubst v sub of
           Just c -> pure (Sym c)
           Nothing ->
             do c <- gen v
                pure (Sym c)
    preProcess' t = pure t

auTheta :: [Term] -> State (Id, Subst [Term] Id) Term
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
                    do z <- gen terms
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
    else let vs = concatMap vars terms
             (terms', sub) = preProcess terms
             invSubst = invertSubst sub
             s = evalState (auTheta terms') (fresh vs, [])  -- Rule 6
         in postProcess s invSubst
