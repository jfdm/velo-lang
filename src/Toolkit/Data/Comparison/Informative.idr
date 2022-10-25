||| An informative notion of comparison
||| This is required by comparison operations where we *need* the
||| equality proof in the `EQ` to be able to further compare subterms.

module Toolkit.Data.Comparison.Informative

%default total

public export
data Comparison : (x : a) -> (y : b) -> Type where
  LT : Comparison x y
  EQ : Comparison x x -- note it's the same `x` in both indices here
  GT : Comparison x y

public export
interface Comparable a b where
  cmp : (x : a) -> (y : b) -> Comparison x y

public export
Comparable Nat Nat where
  cmp Z Z = EQ
  cmp Z (S _) = LT
  cmp (S _) Z = GT
  cmp (S m) (S n) with (cmp m n)
    _ | LT = LT
    cmp (S m) (S .(m)) | EQ = EQ
    _ | GT = GT
