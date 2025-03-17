module Base where

class Unfinite a where
  fresh :: [a] -> a

fresh1 :: Unfinite a => a -> a
fresh1 x = fresh [x]

instance Unfinite Int where
  fresh = succ . maximum

newtype Id = Id String deriving (Eq, Show)

getId :: Id -> String
getId (Id x) = x

instance Unfinite Id where
  fresh ids =
    Id $ if null ids
              then "z"
              else maximum (getId <$> ids) ++ "'"

newtype Sy = Sy String deriving (Eq, Show)

getSy :: Sy -> String
getSy (Sy s) = s

instance Unfinite Sy where
  fresh sys =
    Sy $ if null sys
              then "c"
              else maximum (getSy <$> sys) ++ "'"

