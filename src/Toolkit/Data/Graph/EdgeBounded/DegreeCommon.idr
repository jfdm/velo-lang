|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Graph.EdgeBounded.DegreeCommon

import Decidable.Equality

import Data.String
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Decidable.Do
import Toolkit.Decidable.Informative

import Toolkit.Data.Nat
import Toolkit.Data.Pair
import Toolkit.Data.List.Size
import Toolkit.Data.List.Occurs.Does

%default total

namespace HasDegree

  public export
  data DegreeType = I | O

  public export
  record Error where
    constructor MkError
    vertexID : Nat
    degType  : DegreeType
    values   : Occurs.Error

-- [ EOF ]
