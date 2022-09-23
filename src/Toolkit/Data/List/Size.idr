|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Size

public export
data Size : List a -> Nat -> Type where
  Zero    : Size Nil Z
  PlusOne : Size       rest     k
         -> Size (e :: rest) (S k)

export
size' : (xs : List a) -> DPair Nat (Size xs)
size' [] = MkDPair Z Zero
size' (x :: xs) with (size' xs)
  size' (x :: xs) | (MkDPair k rest) = MkDPair (S k) (PlusOne rest)

export
size : (xs : List a) -> Size xs (length xs)
size [] = Zero
size (x :: xs) = PlusOne (size xs)

Uninhabited (Size Nil (S x)) where
  uninhabited Zero impossible
  uninhabited (PlusOne x) impossible

Uninhabited (Size (x::xs) Z) where
  uninhabited Zero impossible
  uninhabited (PlusOne x) impossible

export
hasSize : (xs : List a) -> (d : Nat) -> Dec (Size xs d)
hasSize xs d with (xs)
  hasSize xs 0 | [] = Yes Zero
  hasSize xs (S k) | [] = No absurd

  hasSize xs 0 | (x :: ys) = No absurd
  hasSize xs (S k) | (x :: ys) with (hasSize ys k)
    hasSize xs (S k) | (x :: ys) | (Yes prf) = Yes (PlusOne prf)
    hasSize xs (S k) | (x :: ys) | (No contra) = No (\(PlusOne y) => contra y)


-- [ EOF ]
