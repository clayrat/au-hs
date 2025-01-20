module AU where

import Data.Maybe (fromMaybe)
import Data.Char (ord, chr)

data Term = Var String
          | Sym String
          | Cons Term Term
          deriving (Eq, Show)

isCons :: Term -> Bool
isCons (Cons _ _) = True
isCons _ = False

type Subst a b = [(a, b)]

genny :: Char -> Int -> String
genny c n = c : '_' : [chr (ord '0' + n)]

lookupSubst :: Eq a => a -> Subst a b -> Maybe b
lookupSubst _   []           = Nothing
lookupSubst key ((k,v):rest) = if key == k then Just v else lookupSubst key rest

invertSubst :: Subst a b -> Subst b a
invertSubst = map (\(x, y) -> (y, x))

preProcess :: [Term] -> ([Term], Subst Term Term)
preProcess terms =
  let (t, s, _) = foldl processOne ([], [], 0) terms in (t, s)
  where
    processOne :: ([Term], Subst Term Term, Int) -> Term -> ([Term], Subst Term Term, Int)
    processOne (accTerms, subst, n) term =
      let (term', subst', n') = preProcess' term subst n
      in (accTerms ++ [term'], subst', n')

    preProcess' :: Term -> Subst Term Term -> Int -> (Term, Subst Term Term, Int)
    preProcess' (Cons a d) subst n =
      let (a', subst' , n' ) = preProcess' a subst  n
          (d', subst'', n'') = preProcess' d subst' n'
      in (Cons a' d', subst'', n'')
    preProcess' v@(Var _) subst n =
      case lookupSubst v subst of
        Just c -> (c, subst, n)
        Nothing -> let c = Sym (genny 'c' n)
                       subst' = (v, c) : subst
                   in (c, subst', n + 1)
    preProcess' t subst n = (t, subst, n)

auTheta :: [Term] -> Subst [Term] Term -> Int -> (Term, Subst [Term] Term, Int)
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
        (x, theta, n)
      ts ->  -- Rule 10
        let z = Var (genny 'z' n)
            theta' = (ts, z) : theta
        in (z, theta', n + 1)

postProcess :: Term -> Subst Term Term -> Term
postProcess   (Cons a d) subst = Cons (postProcess a subst) (postProcess d subst)
postProcess c@(Sym _)    subst = fromMaybe c (lookupSubst c subst)
postProcess t            _     = t

-- Anti-unification
au :: [Term] -> Term
au terms =
  if null terms
    then error "au: |terms| must be > 0"
    else let (terms', subst) = preProcess terms
             (s, _, _) = auTheta terms' [] 0  -- Rule 6
             invSubst = invertSubst subst
         in postProcess s invSubst
