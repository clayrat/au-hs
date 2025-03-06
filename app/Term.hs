module Term where

newtype Id = Id String deriving (Eq, Show)
newtype Sy = Sy String deriving (Eq, Show)

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

occurs :: Id -> Term -> Bool
occurs v (Var x)   = v == x
occurs v (Arr a d) = occurs v a || occurs v d
occurs _ (Sym _)   = False

sub1 :: Id -> Term -> Term -> Term
sub1 v t (Var x)   = if v == x then t else Var x
sub1 v t (Arr a d) = Arr (sub1 v t a) (sub1 v t d)
sub1 _ _ (Sym s)   = Sym s