module AU where

import Data.Maybe (fromMaybe)
import Data.Char (ord, chr)

-- Data types
data Term = Var String
          | Symbol String
          | Cons Term Term
          deriving (Eq, Show)

isVar :: Term -> Bool
isVar (Var _) = True
isVar _ = False

isCons :: Term -> Bool
isCons (Cons _ _) = True
isCons _ = False

genny :: Char -> Int -> String
genny c n = c : '_' : [chr (ord '0' + n)]

-- Custom lookup function that matches Scheme's assq behavior
lookupTerm :: Term -> [(Term, Term)] -> Maybe Term
lookupTerm _ [] = Nothing
lookupTerm key ((k,v):rest) = if key == k then Just v else lookupTerm key rest

-- Custom lookup function for lists of terms
lookupTermList :: [Term] -> [([Term], Term)] -> Maybe Term
lookupTermList _ [] = Nothing
lookupTermList key ((k,v):rest) =
    if length key == length k && and (zipWith (==) key k)
    then Just v
    else lookupTermList key rest

invertSubst :: [(Term, Term)] -> [(Term, Term)]
invertSubst = map (\(x, y) -> (y, x))

-- Pre-processing now handles a list of terms
preProcess :: [Term] -> ([Term], [(Term, Term)])
preProcess terms =
  let (t, s, _) = foldl processOne ([], [], 0) terms in (t, s)
  where
    processOne :: ([Term], [(Term, Term)], Int) -> Term -> ([Term], [(Term, Term)], Int)
    processOne (accTerms, subst, n) term =
      let (term', subst', n') = preProcess' term subst n
      in (accTerms ++ [term'], subst', n')

    preProcess' :: Term -> [(Term, Term)] -> Int -> (Term, [(Term, Term)], Int)
    preProcess' (Cons a d) subst n =
      let (a', subst', n') = preProcess' a subst n
          (d', subst'', n'') = preProcess' d subst' n'
      in (Cons a' d', subst'', n'')
    preProcess' v@(Var _) subst n =
      case lookupTerm v subst of
        Just c -> (c, subst, n)
        Nothing -> let c = Symbol (genny 'c' n)
                       subst' = (v, c) : subst
                  in (c, subst', n + 1)
    preProcess' t subst n = (t, subst, n)

auTheta :: [Term] -> [([Term], Term)] -> Int -> (Term, [([Term], Term)], Int)
auTheta terms theta n =
  if null terms
    then error "auTheta: |terms| must be > 0"
    else case terms of
      (t:ts) | all (== t) ts ->  -- Rule 7
        (t, theta, n)
      ts@(Cons _ _:_) | all isCons ts ->  -- Rule 8
        let (s, theta', n') = auTheta [t1 | Cons t1 _ <- ts] theta n
            (s', theta'', n'') = auTheta [t2 | Cons _ t2 <- ts] theta' n'
        in (Cons s s', theta'', n'')
      ts | Just x <- lookupTermList ts theta ->  -- Rule 9
        (x, theta, n)
      ts ->  -- Rule 10
        let z = Var (genny 'z' n)
            theta' = (ts, z) : theta
        in (z, theta', n + 1)

-- Post-processing
postProcess :: Term -> [(Term, Term)] -> Term
postProcess   (Cons a d) subst = Cons (postProcess a subst) (postProcess d subst)
postProcess c@(Symbol _) subst = fromMaybe c (lookupTerm c subst)
postProcess t            _     = t

-- Anti-unification
au :: [Term] -> Term
au terms =
  if null terms
    then error "au: |terms| must be > 0"
    else let (terms', subst) = preProcess terms
             (s, _, _) = auTheta terms' [] 0
             invSubst = invertSubst subst
         in postProcess s invSubst
