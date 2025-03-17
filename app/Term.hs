module Term where

import Base

data Term = Var Id
          | Sym Sy
          | Arr Term Term
          deriving (Eq, Show)

var :: String -> Term
var = Var . Id

sym :: String -> Term
sym = Sym . Sy

isArr :: Term -> Bool
isArr (Arr _ _) = True
isArr _         = False

syms :: Term -> [Sy]
syms (Var _)   = []
syms (Sym s)   = [s]
syms (Arr a d) = syms a ++ syms d

vars :: Term -> [Id]
vars (Var v)   = [v]
vars (Sym _)   = []
vars (Arr a d) = vars a ++ vars d

occurs :: Id -> Term -> Bool
occurs v (Var x)   = v == x
occurs v (Arr a d) = occurs v a || occurs v d
occurs _ (Sym _)   = False

sub1 :: Id -> Term -> Term -> Term
sub1 v t (Var x)   = if v == x then t else Var x
sub1 v t (Arr a d) = Arr (sub1 v t a) (sub1 v t d)
sub1 _ _ (Sym s)   = Sym s