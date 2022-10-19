module Velo.Types

import Control.Function

import Decidable.Equality

%default total

public export
data Ty = TyNat
        | TyBool
        | TyFunc Ty Ty

export
Show Ty where
  showPrec d TyNat = "Nat"
  showPrec d TyBool = "Bool"
  showPrec d (TyFunc a b) =
    showParens (d > Open) $
      "\{showPrec App a} -> \{show b}"

export
Uninhabited (TyNat = TyBool) where
  uninhabited Refl impossible

export
Uninhabited (TyNat = TyFunc x y) where
  uninhabited Refl impossible

export
Uninhabited (TyBool = TyFunc x y) where
  uninhabited Refl impossible

export
Biinjective TyFunc where
  biinjective Refl = (Refl, Refl)

namespace IsTyFunct

  public export
  data IsTyFunc : Ty -> Type where
    TyFunc : (a, b : Ty) -> IsTyFunc (TyFunc a b)

  export
  isTyFunc : (ty : Ty) -> Maybe (IsTyFunc ty)
  isTyFunc (TyFunc a b) = pure (TyFunc a b)
  isTyFunc _ = Nothing


public export
DecEq Ty where
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

-- [ EOF ]
