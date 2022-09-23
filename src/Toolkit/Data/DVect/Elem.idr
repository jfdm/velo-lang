|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DVect.Elem

import Data.Vect

import Toolkit.Data.DVect

import public Toolkit.Decidable.Equality.Indexed

%default total


public export
data Elem : (iTy : Type)
         -> (elemTy : iTy -> Type)
         -> forall i, is
          . (e : elemTy i)
         -> (es : DVect iTy elemTy l is)
         -> Type
  where
    H : Elem iTy eTy x (y::xs)
    T : (later : Elem iTy eTy x      xs)
             ->  Elem iTy eTy x (x'::xs)

-- [ EOF ]
