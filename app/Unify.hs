module Unify where

import Data.Bifunctor

import Base
import Term
import Subst

type Constr = (Term, Term)

subs1 :: Id -> Term -> [Constr] -> [Constr]
subs1 v t = map (bimap (sub1 v t) (sub1 v t))

data UFail =
    OccL      Id Term
  | OccR      Id Term
  | SymSym    Sy Sy
  | SymArr    Sy Term Term
  | ArrSym    Sy Term Term
  | ArrArrRec UFail
  | EqRec     UFail
  | SubsRecL  UFail
  | SubsRecR  UFail
  deriving (Eq, Show)

unify        :: [Constr] -> Either (Subst Id Term) UFail
unifyNeqHead :: Term -> Term -> [Constr] -> Either (Subst Id Term) UFail

unify []              = Left empSubst
unify ((tl, tr) : cs) =
  if tl == tr
     then second EqRec $
          unify cs
     else unifyNeqHead tl tr cs

unifyNeqHead (Var v)      tr         cs =
  if v `occurs` tr
    then Right (OccL v tr)
    else bimap (insertSubst v tr) SubsRecL $
         unify (subs1 v tr cs)
unifyNeqHead  tl         (Var v)     cs =
  if v `occurs` tl
    then Right (OccR v tl)
    else bimap (insertSubst v tl) SubsRecR $
         unify (subs1 v tl cs)
unifyNeqHead (Arr al dl) (Arr ar dr) cs =
  second ArrArrRec $
  unify ((al, ar) : (dl, dr) : cs)
unifyNeqHead (Arr al dl) (Sym sr)    _  =
  Right (ArrSym sr al dl)
unifyNeqHead (Sym sl)    (Arr ar dr) _  =
  Right (SymArr sl ar dr)
unifyNeqHead (Sym sl)    (Sym sr)    _  =
  Right (SymSym sl sr)

