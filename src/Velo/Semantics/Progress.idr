module Velo.Semantics.Progress

import Decidable.Equality

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term
import Velo.Values
import Velo.Semantics.Reductions

%default total

data Progresss : {tys : List Ty} -> (args : All (Term metas [<]) tys) -> Type
data Progress : (term : Term metas [<] type) -> Type

public export
data Progresss : {tys : List Ty} -> (args : All (Term metas [<]) tys)
              -> Type
  where
    Dones : (vals : Values args)
         -> Progresss args

    Steps : {0 tys : List Ty}
         -> {0 these : All (Term metas [<]) tys}
         -> {those : All (Term metas [<]) tys}
         -> (step : Reduxes these those)
         -> Progresss these

public export
data Progress : (term : Term metas [<] type)
                     -> Type
  where
    Done : forall mty
         . {term : Term metas [<] mty}
        -> (val  : Value term)
                -> Progress term

    Step : {this, that : Term metas [<] type}
        -> (step       : Redux this that)
                      -> Progress this

export
compute : {tys : List Ty}
       -> {0 op : Prim tys ty}
       -> ComputePrim op
       -> {args : All (Term metas [<]) tys}
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
    -> {args : All (Term metas [<]) tys}
    -> Progresss args
    -> Progress (Call p args)
call p (Steps stes) = Step (SimplifyCall p stes)
call p (Dones vals) = case isValuePrim p of
  Left pv => Done (Call pv vals)
  Right npv => compute npv vals

export
progresss : {tys : List Ty}
         -> (args : All (Term metas [<]) tys)
         -> Progresss args
export
progress : {ty   : Ty}
        -> (term : Term metas [<] ty)
        -> Progress term

progresss [] = Dones []
progresss (arg :: args) with (progress arg)
  _ | Step step = Steps (step !: args)
  _ | Done val with (progresss args)
    _ | Dones vals = Dones (val :: vals)
    _ | Steps stes = Steps (val :: stes)

progress (Var v) = absurd v

progress (Met v th)
  = Done Met

progress (Fun body)
  = Done Fun

progress (Call p args) = call p (progresss args)

-- [ EOF ]
