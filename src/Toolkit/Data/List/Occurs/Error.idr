|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Occurs.Error

%default total

namespace Occurs
  public export
  record Error where
    constructor MkError
    expected : Nat
    found    : Nat


-- [ EOF ]
