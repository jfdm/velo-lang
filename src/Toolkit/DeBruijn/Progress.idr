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
import Toolkit.DeBruijn.Reductions
import Toolkit.Item

%default total

public export
interface Reducible type term
       => Valuable (0 type : Type)
                   (0 term : SnocList type -> type -> Type)
                           | term
  where
    public export
    data Value : {0 ty : type} -> term [<] ty -> Type


public export
data Progress : Reducible type term
             -> Valuable  type term
             -> {0 ty : type} -> (that : term [<] ty) -> Type
  where
    Done : (r : Reducible type term)
        => (v : Valuable  type term)
        => forall ty
         . {tm : term [<] ty}
        -> (val : Value tm)
               -> Progress r v tm

    Step : (r : Reducible type term)
        => (v : Valuable  type term)
        => {this, that : term [<] ty}
        -> (step       : Redux this that)
                      -> Progress r v this

public export
interface Progressable (0 type : Type)
                       (0 term : SnocList type -> type -> Type)
                               | term
  where
      progress : (r : Reducible type term)
              => (v : Valuable  type term)
              => {0 ty : type}
              -> (tm : term [<] ty)
                            -> Progress r v tm
{-
-- This type checks but has visibility issues
public export
interface Reducible type term
       => Valuable  type term
       => Progressable (0 type : Type)
                       (0 term : SnocList type -> type -> Type)
                               | term
  where

    mutual
      public export
      data Progress : {0 ty : type} -> (that : term [<] ty) -> Type
        where
          Done : forall ty
               . (tm : term [<] ty)
              -> (val : Value tm)
                     -> Progress tm
          Step : {this, that : term [<] ty}
              -> (step       : Redux this that)
                            -> Progress this

      progress : {ty : type}
              -> (tm : term [<] ty)
                      -> Progress tm


-}
-- [ EOF ]
