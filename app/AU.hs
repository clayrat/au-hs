module AU where

import Control.Monad.State

import Base
import Term
import Subst

uncouple :: Term -> [Term] -> Maybe ((Term, [Term]), (Term, [Term]))
uncouple (Arr p q) ts =
  fmap ((\(ps, qs) -> ((p , ps) , (q , qs))) . unzip) $
  traverse arrSplit ts
uncouple _         _ = Nothing

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

preProcess1 :: Term -> [Term] -> State (Sy, Subst Id Sy) (Term, [Term])
preProcess1 t ts =
  do t' <- preProcessLoop t
     ts' <- mapM preProcessLoop ts
     pure (t', ts')

preProcess :: Term -> [Term] -> (Term, [Term], Subst Id Sy)
preProcess term terms =
  let sys = concatMap syms (term:terms)
      ((t, ts), (_ , s)) = runState (preProcess1 term terms) (fresh sys, empSubst)
  in (t, ts, s)

-- post-processing

postProcess :: Term -> Subst Sy Id -> Term
postProcess   (Arr a d) sub = Arr (postProcess a sub) (postProcess d sub)
postProcess c@(Sym s)   sub = maybe c Var (lookupSubst s sub)
postProcess t           _   = t

-- anti-unification

auTheta :: Term -> [Term] -> State (Id, Subst [Term] Id) Term
auTheta t ts =
  if all (== t) ts then pure t                                -- Rule 7
  else case uncouple t ts of
         Just ((p, ps), (q, qs)) -> do p' <- auTheta p ps     -- Rule 8
                                       q' <- auTheta q qs
                                       pure (Arr p' q')
         Nothing -> do theta <- gets snd
                       case lookupSubst (t:ts) theta of
                         Just x -> pure (Var x)               -- Rule 9
                         Nothing -> do z <- gen (t:ts)        -- Rule 10
                                       pure (Var z)

au :: [Term] -> Maybe Term
au []     = Nothing
au (t:ts) =
  let vs = concatMap vars ts
      (t', ts', sub) = preProcess t ts
      invSubst = invertSubst sub
    in
  Just $
  let s = evalState (auTheta t' ts') (fresh vs, empSubst) in  -- Rule 6
  postProcess s invSubst
