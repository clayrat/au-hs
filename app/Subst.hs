module Subst where

newtype Subst a b = Sub [(a, b)] deriving (Eq, Show)

empSubst :: Subst a b
empSubst = Sub []

insertSubst :: a -> b -> Subst a b -> Subst a b
insertSubst key val (Sub s) = Sub ((key, val) : s)

lookupSubst :: Eq a => a -> Subst a b -> Maybe b
lookupSubst _   (Sub [])           = Nothing
lookupSubst key (Sub ((k,v):rest)) = if key == k then Just v else lookupSubst key (Sub rest)

invertSubst :: Subst a b -> Subst b a
invertSubst (Sub s) = Sub (map (\(x, y) -> (y, x)) s)
