module Toolkit.CoDeBruijn.Variable

import Decidable.Equality

%default total

public export
data IsVar : SnocList a -> a -> Type where
  Here : IsVar [<x] x

export
Uninhabited (IsVar [<] x) where
  uninhabited Here impossible

export
DecEq (IsVar xs x) where
  decEq Here Here = Yes Refl
