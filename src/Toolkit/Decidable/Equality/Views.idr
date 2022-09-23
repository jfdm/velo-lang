|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Decidable.Equality.Views

import Decidable.Equality

import Toolkit.Decidable.Informative

%default total

public export
data AllEqual : (a,b,c : ty) -> Type where
  AE : AllEqual a a a

public export
data Error = AB | AC

abNotEq : (a = b -> Void) -> AllEqual a b c -> Void
abNotEq f AE = f Refl

acNotEq : (a = c -> Void) -> AllEqual a b c -> Void
acNotEq f AE = f Refl

export
allEqual : DecEq type
        => (a,b,c : type)
                 -> DecInfo (Error) (AllEqual a b c)
allEqual a b c with (decEq a b)
  allEqual a a c | (Yes Refl) with (decEq a c)
    allEqual a a a | (Yes Refl) | (Yes Refl) = Yes AE
    allEqual a a c | (Yes Refl) | (No contra)
      = No (AC) (acNotEq contra)
  allEqual a b c | (No contra)
    = No (AB) (abNotEq contra)


-- [ EOF ]
