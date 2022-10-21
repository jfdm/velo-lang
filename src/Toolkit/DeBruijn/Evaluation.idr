||| How to replace things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Evaluation

import Data.Fuel

import public Toolkit.Data.Relation
import public Toolkit.Data.Relation.List
import Toolkit.DeBruijn.Progress

%default total

public export
0 Reduces : (0 redux : Rel a)
         -> (this, that : a)
         -> Type
Reduces redux = RTList redux

public export
data Evaluate : (0 value : Pred a)
             -> (0 redux : Rel a)
             -> (v : a)
             -> Type
  where --
    RunEval : {tm, val : a}
           -> (steps      : Reduces redux tm val)
           -> (result     : Maybe (value val))
                         -> Evaluate value redux tm


export
evaluate : {0 a : Type}
        -> {0 value : Pred a}
        -> {0 redux : Rel a}
        -> Progressable a value redux
        => (fuel : Fuel)
        -> (tm   : a)
                -> Evaluate value redux tm
evaluate Dry term
  = RunEval Nil Nothing
evaluate (More fuel) term with (progress term)
  evaluate (More fuel) term | (Done val)
    = RunEval Nil (Just val)
  evaluate (More fuel) term | (Step step {that}) with (evaluate fuel that)
    evaluate (More fuel) term | (Step step {that = that}) | (RunEval steps result)
      = RunEval (step :: steps) result

public export
data Result : (0 value : Pred a)
           -> (0 redux : Rel a)
           -> (this : a)
           -> Type
  where
    R : (that  : a)
     -> (val   : value that)
     -> (steps : Reduces redux this that)
              -> Result value redux this

export covering
eval : Progressable a value redux
    => (this : a) -> Maybe (Result value redux this)

eval this with (evaluate forever this)
  eval this | (RunEval steps (Just val))
    = Just (R _      -- reduce term is magiced in
              val    -- prf it is a val
              steps)
  eval this | (RunEval steps Nothing) = Nothing

-- [ EOF ]
