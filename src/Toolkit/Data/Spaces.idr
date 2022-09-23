||| Easing working with n-dimensional vectors.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Spaces

import public Decidable.Equality
import Data.Vect

import public Data.Fin
import public Toolkit.Data.DList

import public Toolkit.Data.Vect.Extra

public export
Indices : List Nat -> Type
Indices = DList Nat Fin

-- [ EOF ]
