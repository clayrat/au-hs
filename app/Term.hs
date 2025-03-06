module Term where

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

occurs :: Id -> Term -> Bool
occurs v (Var x)    = v == x
occurs v (Cons a d) = occurs v a || occurs v d
occurs _ (Sym _)    = False

sub :: Id -> Term -> Term -> Term
sub v t (Var x) = if v == x then t else Var x
sub v t (Cons a d) = Cons (sub v t a) (sub v t d)
sub _ _ (Sym s) = Sym s