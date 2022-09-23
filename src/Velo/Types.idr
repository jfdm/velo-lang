module Velo.Types

import Control.Function

import Decidable.Equality

%default total

public export
data Ty = TyNat
        | TyBool
        | TyFunc Ty Ty


Uninhabited (TyNat = TyBool) where
  uninhabited Refl impossible

Uninhabited (TyNat = TyFunc x y) where
  uninhabited Refl impossible

Uninhabited (TyBool = TyFunc x y) where
  uninhabited Refl impossible

Biinjective TyFunc where
  biinjective Refl = (Refl, Refl)


decEq : (x,y : Ty) -> Dec (x === y)
decEq TyNat TyNat
  = Yes Refl

decEq TyNat TyBool
  = No absurd

decEq TyNat (TyFunc x y)
  = No absurd


decEq TyBool TyNat
  = No (negEqSym absurd)

decEq TyBool TyBool
  = Yes Refl

decEq TyBool (TyFunc x y)
  = No absurd

decEq (TyFunc x z) TyNat
  = No (negEqSym absurd)

decEq (TyFunc x z) TyBool
  = No (negEqSym absurd)

decEq (TyFunc aA rA) (TyFunc aB rB)
  = decEqCong2 (decEq aA aB) (decEq rA rB)

export
DecEq Ty where
  decEq = Types.decEq

-- [ EOF ]
