module Velo.Semantics.Progress

import Decidable.Equality

import Velo.Types
import Velo.Terms
import Velo.Values
import Velo.Semantics.Reductions

%default total

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
progress : {ty   : Ty}
        -> (term : Term Nil ty)
                -> Progress term
progress (Var (V _ Here)) impossible
progress (Var (V _ (There later))) impossible

progress (Fun body)
  = Done Fun

progress (App f arg) with (progress f)
  progress (App f arg) | (Done val) with (progress arg)
    progress (App (Fun body) arg) | (Done Fun) | (Done val)
      = Step (ReduceFuncApp val)

    progress (App f arg) | (Done val) | (Step step)
      = Step (SimplifyFuncAppVar val step)

  progress (App f arg) | (Step step)
    = Step (SimplifyFuncAppFunc step)

progress Zero
  = Done Zero

progress (Plus x) with (progress x)
  progress (Plus x) | (Done val)
    = Done (Plus val)

  progress (Plus x) | (Step step)
    = Step (SimplifyPlus step)

progress (Add l r) with (progress l)
  progress (Add l r) | (Done valL) with (progress r)
    progress (Add Zero r) | (Done Zero) | (Done valR)
      = Step (ReduceAddZW valR)

    progress (Add (Plus rest) r) | (Done (Plus x)) | (Done valR)
      = Step (RewriteEqNatPW (Plus x) valR)

    progress (Add l r) | (Done valL) | (Step step)
      = Step (SimplifyAddRight valL step)

  progress (Add l r) | (Step step)
    = Step (SimplifyAddLeft step)

progress True
  = Done True
progress False
  = Done False

progress (And l r) with (progress l)
  progress (And l r) | (Done valL) with (progress r)
    progress (And True True) | (Done True) | (Done True)
      = Step ReduceAndTT

    progress (And True False) | (Done True) | (Done False)
      = Step ReduceAndWF

    progress (And False r) | (Done False) | (Done valR)
      = Step ReduceAndFW

    progress (And True r) | (Done True) | (Step step)
      = Step (SimplifyAndRight True step)

    progress (And False r) | (Done False) | (Step step)
      = Step ReduceAndFW

  progress (And l r) | (Step step)
    = Step (SimplifyAndLeft step)



-- [ EOF ]
