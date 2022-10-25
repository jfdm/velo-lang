module Toolkit.CoDeBruijn.Binding

import Control.Function
import Decidable.Equality

%default total

public export
data Binding : (t : SnocList a -> Type) -> a -> SnocList a -> Type where
  ||| Constant
  K : t g -> Binding t s g
  ||| Relevant
  R : (0 s : a) -> t (g :< s) -> Binding t s g

export Injective (K {t, s, g}) where injective Refl = Refl
export Injective (R {t, g} s) where injective Refl = Refl

export Uninhabited (K {t, s, g} l === R s r) where uninhabited Refl impossible
export Uninhabited (R {t, g} s l === K r) where uninhabited Refl impossible

public export
({0 xs : SnocList a} -> DecEq (t xs)) => DecEq (Binding t x xs) where
  decEq (K t) (K u) = decEqCong (decEq t u)
  decEq (K _) (R _ _) = No absurd
  decEq (R _ _) (K _) = No absurd
  decEq (R x t) (R x u) = decEqCong (decEq t u)

public export
(forall xs. Eq (t xs)) => Eq (Binding t x xs) where
  K t == K u = t == u
  R x t == R x u = t == u
  _ == _ = False

public export
(forall xs. Ord (t xs)) => Ord (Binding t x xs) where
  compare (K t) (K u) = compare t u
  compare (K _) _ = LT
  compare _ (K _) = GT
  compare (R x t) (R x u) = compare t u
