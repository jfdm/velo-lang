|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Pair

import Decidable.Equality

%default total

public export
data IsFirst : (this : a) -> (that : Pair a b) -> Type where
  IF : (prf : x = y)
    -> IsFirst x (y,b)

export
isFirst : DecEq type
       => (this : type)
       -> (that : Pair type b)
               -> Dec (IsFirst this that)
isFirst this (x, y) with (decEq this x)
  isFirst this (this, y) | (Yes Refl)
    = Yes (IF Refl)
  isFirst this (x, y) | (No contra)
    = No (\(IF Refl) => contra Refl)

public export
data IsSecond : (this : b) -> (that : Pair a b) -> Type where
  IS : (prf : x = y)
    -> IsSecond x (a,y)

export
isSecond : DecEq type
        => (this : type)
        -> (that : Pair a type)
                -> Dec (IsSecond this that)
isSecond this (x, y) with (decEq this y)
  isSecond this (x, this) | (Yes Refl)
    = Yes (IS Refl)
  isSecond this (x, y) | (No contra)
    = No (\(IS Refl) => contra Refl)

-- [ EOF ]
