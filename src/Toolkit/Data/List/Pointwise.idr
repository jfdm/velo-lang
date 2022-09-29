module Toolkit.Data.List.Pointwise

%default total

public export
data Pointwise : (r : a -> b -> Type) -> List a -> List b -> Type where
  Nil : Pointwise r [] []
  (::) : {0 r : a -> b -> Type} ->
         r x y ->
         Pointwise r xs ys ->
         Pointwise r (x :: xs) (y :: ys)
