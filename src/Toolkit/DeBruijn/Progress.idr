||| How to replace things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Progress

import Decidable.Equality

import Data.DPair
import Data.SnocList

import Toolkit.Decidable.Informative

import Toolkit.DeBruijn.Variable
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming
import Toolkit.DeBruijn.Substitution
import Toolkit.Item

%default total

public export
data Progress : (0 type : Type)
             -> (0 term : SnocList type -> type -> Type)

             -> (0 value : {0 ty : type} -> (value : term [<] ty) -> Type)
             -> (0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type)
             -> {0 ty : type}
             -> (that : term [<] ty) -> Type
  where
    Done : {0 type : Type}
        -> {0 term : SnocList type -> type -> Type}

        -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
        -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}
        -> forall ty
         . {tm : term [<] ty}
        -> (val : value tm)
               -> Progress type term value redux tm

    Step : {0 type : Type}
        -> {0 term : SnocList type -> type -> Type}

        -> {0 value : {0 ty : type} -> (value : term [<] ty) -> Type}
        -> {0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type}
        -> forall ty
         . {this, that : term [<] ty}
        -> (step       : redux this that)
                      -> Progress type term value redux this


public export
interface Progressable (0 type : Type)
                       (0 term : SnocList type -> type -> Type)
                       (0 value : {0 ty : type} -> (v : term [<] ty) -> Type)
                       (0 redux : {0 ty : type} -> (this, that : term [<] ty) -> Type)
                               | term
  where
      progress : forall ty
               . (tm : term [<] ty)
                    -> Progress type term value redux tm

-- [ EOF ]
