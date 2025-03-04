module AU where

import Control.Monad.State
import Data.Char (ord, chr)

newtype Id = Id String deriving (Eq, Show)
newtype Sy = Sy String deriving (Eq, Show)

data Term = Var Id
          | Sym Sy
          | Cons Term Term
          deriving (Eq, Show)

var :: String -> Term
var = Var . Id

sym :: String -> Term
sym = Sym . Sy

isCons :: Term -> Bool
isCons (Cons _ _) = True
isCons _          = False

type Subst a b = [(a, b)]

gen :: Char -> (String -> b) -> a -> State (Int, Subst a b) b
gen c f a = do
  (n, s) <- get
  let b = f (c : '_' : [chr (ord '0' + n)])
  put (n + 1, (a, b) : s)
  return b

lookupSubst :: Eq a => a -> Subst a b -> Maybe b
lookupSubst _   []           = Nothing
lookupSubst key ((k,v):rest) = if key == k then Just v else lookupSubst key rest

invertSubst :: Subst a b -> Subst b a
invertSubst = map (\(x, y) -> (y, x))

preProcess :: [Term] -> ([Term], Subst Id Sy)
preProcess terms =
  let (t, (_ , s)) = runState (mapM preProcess' terms) (0, [])
  in (t , s)
  where
    preProcess' :: Term -> State (Int, Subst Id Sy) Term
    preProcess' (Cons a d) =
      do a' <- preProcess' a
         d' <- preProcess' d
         pure (Cons a' d')
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
              ts | all isCons ts ->  -- Rule 8
                do s  <- auTheta [t1 | Cons t1 _ <- ts]
                   s' <- auTheta [t2 | Cons _ t2 <- ts]
                   pure (Cons s s')
              ts ->
                case lookupSubst ts theta of
                  Just x -> pure (Var x) -- Rule 9
                  Nothing ->  -- Rule 10
                    do z <- gen 'z' Id terms
                       pure (Var z)

postProcess :: Term -> Subst Sy Id -> Term
postProcess   (Cons a d) subst = Cons (postProcess a subst) (postProcess d subst)
postProcess c@(Sym s)    subst = maybe c Var (lookupSubst s subst)
postProcess t            _     = t

-- Anti-unification
au :: [Term] -> Term
au terms =
  if null terms
    then error "au: |terms| must be > 0"
    else let (terms', subst) = preProcess terms
             invSubst = invertSubst subst
             s = evalState (auTheta terms') (0, [])  -- Rule 6
         in postProcess s invSubst
