||| How to replace things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Evaluation

import Decidable.Equality

import Data.DPair
import Data.SnocList

import Data.Fuel

import Toolkit.Decidable.Informative

import Toolkit.DeBruijn.Variable
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming
import Toolkit.DeBruijn.Substitution
import Toolkit.DeBruijn.Reductions
import Toolkit.DeBruijn.Progress
import Toolkit.Item

%default total

data Finished : Reducible type term
             -> Valuable  type term
             -> Progressable type term
             -> (tm : term ctxt ty)
                     -> Type
  where
    Normalised : (r : Reducible    type term)
           => (v : Valuable     type term)
           => (p : Progressable type term)
               => {tm : term [<] ty}
               -> Value tm
               -> Finished r v p tm
    OOF : (r : Reducible    type term)
           => (v : Valuable     type term)
           => (p : Progressable type term)
        => Finished r v p tm

data Evaluate : Reducible type term
             -> Valuable  type term
             -> Progressable type term
             -> (tm : term [<] ty)
                   -> Type
  where --
    RunEval : (r : Reducible    type term)
           => (v : Valuable     type term)
           => (p : Progressable type term)
           => {this, that : term [<] ty}
           -> (steps      : Inf (Reduces r this that))
           -> (result     : Finished r v p that)
                         -> Evaluate r v p this


export
evaluate : (r : Reducible    type term)
        => (v : Valuable     type term)
        => (p : Progressable type term)
        => (fuel : Fuel)
        -> (tm   : term [<] ty)
                -> Evaluate r v p tm
evaluate Dry term
  = RunEval Refl OOF
evaluate (More fuel) term with (progress term)
  evaluate (More fuel) term | (Done value)
    = RunEval Refl (Normalised value)
  evaluate (More fuel) term | (Step step {that}) with (evaluate fuel that)
    evaluate (More fuel) term | (Step step {that = that}) | (RunEval steps result)
      = RunEval (Trans step steps) result

public export
data Result : Reducible type term
           -> Valuable  type term
           -> Progressable type term
           -> (tm : term [<] ty) -> Type where
  R : (r : Reducible    type term)
   => (v : Valuable     type term)
   => (p : Progressable type term)
   => (that : term [<] ty)
   -> (val   : Value that)
   -> (steps : Reduces r this that)
              -> Result r v p this

export covering
eval : (r    : Reducible    type term)
    => (v    : Valuable     type term)
    => (p    : Progressable type term)
    => forall ty
     . (this : term [<] ty)
            -> Maybe (Result r v p this)

eval this with (evaluate forever this)
  eval this | (RunEval steps (Normalised {tm} x))
    = Just (R tm x steps)
  eval this | (RunEval steps OOF) = Nothing

-- [ EOF ]
