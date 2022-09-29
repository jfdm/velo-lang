module Velo.Semantics.Progress

import Decidable.Equality

import Velo.Types
import Velo.Terms
import Velo.Values
import Velo.Semantics.Reductions

%default total

data Progresss : (args : All (Term Nil) tys) -> Type
data Progress : (term : Term Nil type) -> Type

public export
data Progresss : (args : All (Term Nil) tys)
              -> Type
  where
    Dones : (vals : Values args)
         -> Progresss args

    Steps : {those : All (Term Nil) tys}
         -> (step : Reduxes these those)
         -> Progresss these

public export
data Progress : (term : Term Nil type)
                     -> Type
  where
    Done : forall mty
         . {term : Term Nil mty}
        -> (val  : Value term)
                -> Progress term

    Step : {this, that : Term Nil type}
        -> (step       : Redux this that)
                      -> Progress this

export
compute : {tys : List Ty}
       -> {0 op : Prim tys ty}
       -> ComputePrim op
       -> {args : All (Term Nil) tys}
       -> Values args
       -> Progress (Call op args)
compute Add [m, n] = case m of
  Call Zero [] => Step (ReduceAddZW n)
  Call Plus [m] => Step (RewriteEqNatPW (Call Plus [m]) n)
  Call True _  impossible
  Call False _  impossible

compute And [b, c] = case b of
  Call False [] => Step ReduceAndFW
  Call True [] => case c of
    Call False [] => Step ReduceAndWF
    Call True [] => Step ReduceAndTT
    Call Zero _ impossible
    Call Plus _ impossible
  Call Zero _ impossible
  Call Plus _ impossible

compute App [f, t] = case f of
  Fun => Step (ReduceFuncApp t)
  Call _ _ impossible

export
call : {tys : _}
    -> (p : Prim tys ty)
    -> {args : All (Term Nil) tys}
    -> Progresss args
    -> Progress (Call p args)
call p (Steps stes) = Step (SimplifyCall p stes)
call p (Dones vals) = case isValuePrim p of
  Left pv => Done (Call pv vals)
  Right npv => compute npv vals

export
progresss : {tys : List Ty}
         -> (args : All (Term Nil) tys)
         -> Progresss args
export
progress : {ty   : Ty}
        -> (term : Term Nil ty)
                -> Progress term

progresss [] = Dones []
progresss (arg :: args) with (progress arg)
  _ | Step step = Steps (step !: args)
  _ | Done val with (progresss args)
    _ | Dones vals = Dones (val :: vals)
    _ | Steps stes = Steps (val :: stes)

progress (Var (V _ Here)) impossible
progress (Var (V _ (There later))) impossible

progress (Fun body)
  = Done Fun

progress (Call p args) = call p (progresss args)

-- [ EOF ]
