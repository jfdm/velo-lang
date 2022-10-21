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

import public Toolkit.Data.Relation
import public Toolkit.Data.Relation.List

import Toolkit.DeBruijn.Variable
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming
import Toolkit.DeBruijn.Substitution

import Toolkit.DeBruijn.Progress
import Toolkit.Item

%default total

public export
data Reduces : (0 type : Type)
            -> (0 term : SnocList type -> type -> Type)

            -> (0 value : {0 ty : type} -> (value : term [<] ty) -> Type)
            -> (0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type)

            -> {0 ty : type}
            -> (  this : term [<] ty)
            -> (  that : term [<] ty)
                      -> Type
  where
    RS : {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
      -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}
      -> forall ty . {this, that : term [<] ty}
      -> RTList redux this that
      -> Reduces type term value redux this that

data Evaluate : (0 type : Type)
             -> (0 term : SnocList type -> type -> Type)

             -> (0 value : {0 ty : type} -> (value : term [<] ty) -> Type)
             -> (0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type)

             -> forall ty . (tm : term [<] ty)
             -> Type
  where --
    RunEval : {0 type : Type}
           -> {0 term : SnocList type -> type -> Type}

           -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
           -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}

           -> forall ty . {this, that : term [<] ty}
           -> (steps      : Inf (Reduces type term value redux this that))
           -> (result     : Maybe (value that))
                         -> Evaluate type term value redux this


export
evaluate : {0 type : Type}
           -> {0 term : SnocList type -> type -> Type}

           -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
           -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}
           -> Progressable type term value redux
        => (fuel : Fuel)
        -> forall ty .
           (tm   : term [<] ty)
                -> Evaluate type term value redux tm
evaluate Dry term
  = RunEval (RS Nil) Nothing
evaluate (More fuel) term with (progress term)
  evaluate (More fuel) term | (Done val)
    = RunEval (RS Nil) (Just val)
  evaluate (More fuel) term | (Step step {that}) with (evaluate fuel that)
    evaluate (More fuel) term | (Step step {that = that}) | (RunEval (RS steps) result)
      = RunEval (RS (step :: steps)) result

public export
data Result : (0 type : Type)
           -> (0 term : SnocList type -> type -> Type)

           -> (0 value : {0 ty : type} -> (value : term [<] ty) -> Type)
           -> (0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type)
           -> forall ty
            . (tm : term [<] ty)
           -> Type
  where
    R : {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
     -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}

     -> (that : term [<] ty)
     -> (val   : value that)
     -> (steps : Reduces type term value redux this that)
              -> Result type term value redux this


export covering
eval :  {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
     -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}

     -> Progressable type term value redux
    => forall ty
     . (this : term [<] ty)
            -> Maybe (Result type term value redux this)


eval this with (evaluate forever this)
  eval this | (RunEval steps (Just val))
    = Just (R _      -- reduce term is magiced in
              val    -- prf it is a val
              steps)
  eval this | (RunEval steps Nothing) = Nothing

-- [ EOF ]
