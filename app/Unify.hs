module Unify where

import Data.Bifunctor
import Term
import Subst

type Constr = (Term, Term)

subs1 :: Id -> Term -> [Constr] -> [Constr]
subs1 v t = map (bimap (sub1 v t) (sub1 v t))

data UFail =
    OccFailL  Id Term
  | OccFailR  Id Term
  | SymSym    Sy Sy
  | SymArr    Sy Term Term
  | ArrSym    Sy Term Term
  | ArrArrRec UFail
  | EqRec     UFail
  | SubsRecL  UFail
  | SubsRecR  UFail
  deriving (Eq, Show)

unify :: [Constr] -> Either (Subst Id Term) UFail
unify []              = Left []
unify ((tl, tr) : cs) =
  if tl == tr
     then second EqRec (unify cs)
     else case (tl, tr) of
           (Var v, _) ->
              if v `occurs` tr
                 then Right (OccFailL v tr)
                 else bimap (\s -> (v, tr) : s) SubsRecL (unify (subs1 v tr cs))
           (_, Var v) ->
              if v `occurs` tl
                 then Right (OccFailR v tl)
                 else bimap (\s -> (v, tl) : s) SubsRecR (unify (subs1 v tl cs))
           (Arr al dl, Arr ar dr) ->
              second ArrArrRec (unify ((al, ar) : (dl, dr) : cs))
           (Arr al dl, Sym sr) ->
              Right (ArrSym sr al dl)
           (Sym sl, Arr ar dr) ->
              Right (SymArr sl ar dr)
           (Sym sl, Sym sr) ->
              Right (SymSym sl sr)

