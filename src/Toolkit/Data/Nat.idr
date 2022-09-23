|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Nat

import Decidable.Equality

%default total

public export
toNat : Int -> Nat
toNat = (integerToNat . cast)


public export
data Plus : (x,y,z : Nat) -> Type where
  Zero : Plus Z y y
  One  : Plus    n  x    z
      -> Plus (S n) x (S z)

export
plus : (x,y : Nat) -> DPair Nat (Plus x y)
plus Z y
  = MkDPair y Zero

plus (S k) y with (Nat.plus k y)
  plus (S k) y | (MkDPair fst snd)
    = MkDPair (S fst) (One snd)


resWhenZeroIsMore : (y = z -> Void) -> Plus 0 y z -> Void
resWhenZeroIsMore f Zero = f Refl

resWhenOneIsZero :  Plus (S k) y 0 -> Void
resWhenOneIsZero Zero impossible
resWhenOneIsZero (One x) impossible

export
isPlus : (x,y,z : Nat) -> Dec (Plus x y z)
isPlus Z y z with (decEq y z)
  isPlus Z y y | (Yes Refl)
    = Yes Zero

  isPlus Z y z | (No contra)
    = No (resWhenZeroIsMore contra)

isPlus (S k) y 0 = No resWhenOneIsZero

isPlus (S k) y (S j) with (isPlus k y j)
  isPlus (S k) y (S j) | (Yes prf)
    = Yes (One prf)

  isPlus (S k) y (S j) | (No contra)
    = No (\(One prf) => contra prf)

-- [ EOF ]
