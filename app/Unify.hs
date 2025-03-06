module Unify where

import Data.Bifunctor
import Term
import Subst

type Constr = (Term, Term)

subs :: Id -> Term -> [Constr] -> [Constr]
subs v t = map (bimap (sub v t) (sub v t))

data UFail =
    OccFailL  Id Term
  | OccFailR  Id Term
  | ConCon    Sy Sy
  | ConArr    Sy Term Term
  | ArrCon    Sy Term Term
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
                 else bimap (\s -> (v, tr) : s) SubsRecL (unify (subs v tr cs))
           (_, Var v) ->
              if v `occurs` tl
                 then Right (OccFailR v tr)
                 else bimap (\s -> (v, tl) : s) SubsRecR (unify (subs v tl cs))
           (Cons al dl, Cons ar dr) ->
              second ArrArrRec (unify ((al, ar) : (dl, dr) : cs))
           (Cons al dl, Sym sr) ->
              Right (ArrCon sr al dl)
           (Sym sl, Cons ar dr) ->
              Right (ConArr sl ar dr)
           (Sym sl, Sym sr) ->
              Right (ConCon sl sr)

