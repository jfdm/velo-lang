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
    Refl : {0 type : Type}
        -> {0 term : SnocList type -> type -> Type}

        -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
        -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}
        -> forall ty . {this : term [<] ty}
                -> Reduces type term value redux this this

    Trans : {0 type : Type}
        -> {0 term : SnocList type -> type -> Type}

        -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
        -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}
        -> forall ty . {this, that, end : term [<] ty}
         -> redux     this that
         -> Reduces type term value redux      that   end
         -> Reduces type term value redux this        end

data Finished : (0 type : Type)
             -> (0 term : SnocList type -> type -> Type)

             -> (0 value : {0 ty : type} -> (value : term [<] ty) -> Type)
             -> (0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type)
             -> forall ty . (tm : term [<] ty)
                     -> Type
  where
    Normalised : {0 type : Type}
        -> {0 term : SnocList type -> type -> Type}

        -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
        -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}
        -> forall ty . {tm : term [<] ty}
               -> value tm
               -> Finished type term value redux tm

    OOF :  {0 type : Type}
        -> {0 term : SnocList type -> type -> Type}

        -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
        -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}

        -> forall ty . {tm : term [<] ty}
        -> Finished type term value redux tm

data Evaluate : (0 type : Type)
             -> (0 term : SnocList type -> type -> Type)

             -> (0 value : {0 ty : type} -> (value : term [<] ty) -> Type)
             -> (0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type)

             -> forall ty .
                (tm : term [<] ty)
                   -> Type
  where --
    RunEval : {0 type : Type}
           -> {0 term : SnocList type -> type -> Type}

           -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
           -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}

           -> forall ty .
            {this, that : term [<] ty}
           -> (steps      : Inf (Reduces type term value redux this that))
           -> (result     : Finished type term value redux that)
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
  = RunEval Refl OOF
evaluate (More fuel) term with (progress term)
  evaluate (More fuel) term | (Done val)
    = RunEval Refl (Normalised val)
  evaluate (More fuel) term | (Step step {that}) with (evaluate fuel that)
    evaluate (More fuel) term | (Step step {that = that}) | (RunEval steps result)
      = RunEval (Trans step steps) result

public export
data Result : (0 type : Type)
             -> (0 term : SnocList type -> type -> Type)

             -> (0 value : {0 ty : type} -> (value : term [<] ty) -> Type)
             -> (0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type)
             -> forall ty . (tm : term [<] ty) -> Type where
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
  eval this | (RunEval steps (Normalised {tm} x))
    = Just (R tm x steps)
  eval this | (RunEval steps OOF) = Nothing

-- [ EOF ]
