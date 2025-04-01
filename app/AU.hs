module AU where

import Control.Monad.State

import Base
import Term
import Subst

unreplicate :: [Term] -> Maybe Term
unreplicate []     = Nothing
unreplicate (t:ts) = if all (== t) ts then Just t else Nothing

uncouple :: [Term] -> Maybe ([Term], [Term])
uncouple ts = unzip <$> traverse arrSplit ts

gen :: Unfinite b => a -> State (b, Subst a b) b
gen a = do
  (x, s) <- get
  put (fresh1 x, insertSubst a x s)
  pure x

-- pre-processing

preProcessLoop :: Term -> State (Sy, Subst Id Sy) Term
preProcessLoop (Arr a d) =
  do a' <- preProcessLoop a
     d' <- preProcessLoop d
     pure (Arr a' d')
preProcessLoop (Var v) =
  do sub <- gets snd
     case lookupSubst v sub of
       Just c -> pure (Sym c)
       Nothing ->
         do c <- gen v
            pure (Sym c)
preProcessLoop t = pure t

preProcess :: [Term] -> ([Term], Subst Id Sy)
preProcess terms =
  let sys = concatMap syms terms
      st = traverse preProcessLoop terms
      (ts, (_ , s)) = runState st (fresh sys, empSubst)
  in (ts, s)

-- post-processing

postProcess :: Term -> Subst Sy Id -> Term
postProcess   (Arr a d) sub = Arr (postProcess a sub) (postProcess d sub)
postProcess c@(Sym s)   sub = maybe c Var (lookupSubst s sub)
postProcess t           _   = t

-- anti-unification

type AUTy = State (Id, Subst [Term] Id) Term

auArr :: AUTy -> AUTy -> AUTy
auArr x y =
  do p <- x
     q <- y
     pure (Arr p q)

auMiss :: [Term] -> AUTy
auMiss ts =
  do theta <- gets snd
     case lookupSubst ts theta of
       Just x -> pure (Var x)                                 -- Rule 9
       Nothing -> do z <- gen ts                              -- Rule 10
                     pure (Var z)

auTheta :: [Term] -> AUTy
auTheta ts =
  case unreplicate ts of
    Just t  -> pure t                                         -- Rule 7
    Nothing ->
      case uncouple ts of
        Just (ps, qs) -> auArr (auTheta ps) (auTheta qs)      -- Rule 8
        Nothing       -> auMiss ts

au :: [Term] -> Maybe Term
au []       = Nothing
au ts@(_:_) =
  let vs = ts >>= vars
      (ts', sub) = preProcess ts
      isub = invertSubst sub
      at = auTheta ts'                                       -- Rule 6
      s = evalState at (fresh vs, empSubst)
    in
  Just $ postProcess s isub
