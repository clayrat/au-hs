module AU where

import Data.Maybe (maybe)
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
isCons _ = False

type Subst a b = [(a, b)]

genid :: Int -> Id
genid n = Id ("z_" ++ [chr (ord '0' + n)])

gensy :: Int -> Sy
gensy n = Sy ("c_" ++ [chr (ord '0' + n)])

lookupSubst :: Eq a => a -> Subst a b -> Maybe b
lookupSubst _   []           = Nothing
lookupSubst key ((k,v):rest) = if key == k then Just v else lookupSubst key rest

invertSubst :: Subst a b -> Subst b a
invertSubst = map (\(x, y) -> (y, x))

preProcess :: [Term] -> ([Term], Subst Id Sy)
preProcess terms =
  let (t, s, _) = foldl processOne ([], [], 0) terms in (t, s)
  where
    processOne :: ([Term], Subst Id Sy, Int) -> Term -> ([Term], Subst Id Sy, Int)
    processOne (accTerms, subst, n) term =
      let (term', subst', n') = preProcess' term subst n
      in (accTerms ++ [term'], subst', n')

    preProcess' :: Term -> Subst Id Sy -> Int -> (Term, Subst Id Sy, Int)
    preProcess' (Cons a d) subst n =
      let (a', subst' , n' ) = preProcess' a subst  n
          (d', subst'', n'') = preProcess' d subst' n'
      in (Cons a' d', subst'', n'')
    preProcess' (Var v) subst n =
      case lookupSubst v subst of
        Just c -> (Sym c, subst, n)
        Nothing -> let c = gensy n
                       subst' = (v, c) : subst
                   in (Sym c, subst', n + 1)
    preProcess' t subst n = (t, subst, n)

auTheta :: [Term] -> Subst [Term] Id -> Int -> (Term, Subst [Term] Id, Int)
auTheta terms theta n =
  if null terms
    then error "auTheta: |terms| must be > 0"
    else case terms of
      (t:ts) | all (== t) ts ->  -- Rule 7
        (t, theta, n)
      ts | all isCons ts ->  -- Rule 8
        let (s , theta' , n' ) = auTheta [t1 | Cons t1 _ <- ts] theta  n
            (s', theta'', n'') = auTheta [t2 | Cons _ t2 <- ts] theta' n'
        in (Cons s s', theta'', n'')
      ts | Just x <- lookupSubst ts theta ->  -- Rule 9
        (Var x, theta, n)
      ts ->  -- Rule 10
        let z = genid n
            theta' = (ts, z) : theta
        in (Var z, theta', n + 1)

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
             (s, _, _) = auTheta terms' [] 0  -- Rule 6
         in postProcess s invSubst
