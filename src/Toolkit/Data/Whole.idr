|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Whole

import Decidable.Equality

import Data.Nat

%default total

public export
data Whole : Type where
  W : (n : Nat) -> (prf : IsSucc n) -> Whole


public export
data IsOne : Whole -> Type where
  ItIsOne : IsOne (W (S Z) ItIsSucc)

wholeIsNotOne : Not (IsOne $ W (S (S n)) ItIsSucc)
wholeIsNotOne ItIsOne impossible

export
isOne : (w : Whole) -> Dec (IsOne w)
isOne (W n prf) with (prf)
  isOne (W (S k) prf) | ItIsSucc with (k)
    isOne (W (S k) prf) | ItIsSucc | Z = Yes ItIsOne
    isOne (W (S k) prf) | ItIsSucc | (S j) = No wholeIsNotOne

public export
data IsGreaterThanOne : Whole -> Type where
  IsGT1 : (LTE 2 (S n)) -> IsGreaterThanOne (W (S n) ItIsSucc)

wholeIsOne : Not (IsGreaterThanOne $ W (S Z) ItIsSucc)
wholeIsOne (IsGT1 (LTESucc LTEZero)) impossible
wholeIsOne (IsGT1 (LTESucc (LTESucc _))) impossible

decEqWholeNotEqual : (contra : (k = j) -> Void) -> (W (S k) ItIsSucc = W (S j) ItIsSucc) -> Void
decEqWholeNotEqual contra Refl = contra Refl

export
isGreaterThanOne : (w : Whole) -> Dec (IsGreaterThanOne w)
isGreaterThanOne (W n prf) with (prf)
  isGreaterThanOne (W (S k) prf) | ItIsSucc with (isLTE 2 (S k))
    isGreaterThanOne (W (S k) prf) | ItIsSucc | (Yes x) = Yes (IsGT1 x)
    isGreaterThanOne (W (S k) prf) | ItIsSucc | (No contra) with (k)
      isGreaterThanOne (W (S k) prf) | ItIsSucc | (No contra) | Z = No wholeIsOne
      isGreaterThanOne (W (S k) prf) | ItIsSucc | (No contra) | (S j) = Yes (IsGT1 (LTESucc (LTESucc LTEZero)))

export
DecEq Whole where
  decEq (W (S k) ItIsSucc) (W (S j) ItIsSucc) with (decEq k j)
    decEq (W (S j) ItIsSucc) (W (S j) ItIsSucc) | (Yes Refl) = Yes Refl
    decEq (W (S k) ItIsSucc) (W (S j) ItIsSucc) | (No contra) = No (decEqWholeNotEqual contra)

export
Show Whole where
  show (W n prf) = show n

export
toNat : Whole -> Nat
toNat (W n prf) = n

namespace Auto
  export
  fromNat : (x : Nat) -> {auto prf : IsSucc x} -> Whole
  fromNat x {prf} = W x prf

public export
data LT : Whole -> Whole -> Type where
  IsLT : (prf : LT min max)
       -> LT (W min prfA) (W max prfB)

isNotLT : (LTE (S n) k -> Void) -> LT (W n prf) (W k x) -> Void
isNotLT f (IsLT y) = f y

export
isLT : (a,b : Whole) -> Dec (LT a b)
isLT (W n prf) (W k x) with (isLTE (S n) k)
  isLT (W n prf) (W k x) | (Yes y) = Yes (IsLT y)
  isLT (W n prf) (W k x) | (No contra) = No (isNotLT contra)

public export
data LTE : Whole -> Whole -> Type where
  IsLTE : (prf : LTE min max)
       -> LTE (W min prfA) (W max prfB)


isLTENot : (contra : LTE n k -> Void)
        -> LTE (W n prf) (W k x) -> Void
isLTENot contra (IsLTE y) = contra y

export
isLTE : (a,b : Whole) -> Dec (LTE a b)
isLTE (W n prf) (W k x) with (isLTE n k)
  isLTE (W n prf) (W k x) | (Yes y) = Yes (IsLTE y)
  isLTE (W n prf) (W k x) | (No contra) = No (isLTENot contra)

export
Eq Whole where
  (W l prfL) == (W r prfR) = l == r

export
Ord Whole where
  compare (W l prfL) (W r prfR) = compare l r

namespace IsLteNatWhole

  public export
  data LTE : Nat -> Whole -> Type where
    IsLTE : (prf : LTE min max)
                -> LTE min (W max prfMax)

  isLTENot : (LTE n k -> Void) -> IsLteNatWhole.LTE n (W k prf) -> Void
  isLTENot f (IsLTE x) = f x

  export
  isLTE : (n : Nat) -> (w : Whole) -> Dec (LTE n w)
  isLTE n (W k prf) with (isLTE n k)
    isLTE n (W k prf) | (Yes x) = Yes (IsLTE x)
    isLTE n (W k prf) | (No contra) = No (isLTENot contra)

namespace Nat
  public export
  data IsWhole : Nat -> Type where
    YesIsWhole : IsWhole (S n)

  isZero : IsWhole 0 -> Void
  isZero YesIsWhole impossible


  export
  isWhole : (n : Nat) -> Dec (IsWhole n)
  isWhole 0 = No isZero
  isWhole (S k) = Yes YesIsWhole




-- --------------------------------------------------------------------- [ EOF ]
