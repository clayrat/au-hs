module Subst where

type Subst a b = [(a, b)]

lookupSubst :: Eq a => a -> Subst a b -> Maybe b
lookupSubst _   []           = Nothing
lookupSubst key ((k,v):rest) = if key == k then Just v else lookupSubst key rest

invertSubst :: Subst a b -> Subst b a
invertSubst = map (\(x, y) -> (y, x))
