|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Location

import Toolkit.Data.Nat

%default total

public export
record Location where
  constructor MkLoc
  source : Maybe String
  line   : Nat
  col    : Nat

public export
record FileContext where
  constructor MkFC
  source : Maybe String
  start  : Location
  end    : Location

public export
record Ref where
  constructor MkRef
  span : FileContext
  get  : String


public export
FC : Type
FC = FileContext

export
newFC : Maybe String -> Location -> Location -> FileContext
newFC n s e = MkFC n ({source := n} s) ({source := n} e)

namespace FromCoords
  export
  newLoc : Maybe String -> (Nat, Nat) -> Location
  newLoc n (l,c) = MkLoc n l c

  export
  newFC : Maybe String -> (Nat, Nat) -> (Nat, Nat) -> FileContext
  newFC n s e = newFC n (newLoc n s) (newLoc n e)

  namespace Int
    export
    newLoc : Maybe String -> (Int, Int) -> Location
    newLoc n (l,c) = newLoc n (toNat l, toNat c)

    export
    newFC : Maybe String -> (Int , Int) -> (Int, Int) -> FileContext
    newFC n s e = newFC n (newLoc n s) (newLoc n e)

namespace Anon

  export
  newLoc : (Nat, Nat) -> Location
  newLoc (l,c) = MkLoc Nothing l c

  export
  newFC : Location -> Location -> FileContext
  newFC s e = newFC Nothing s e

export
emptyFC : FileContext
emptyFC = newFC Nothing (Z,Z) (Z,Z)

export
setSource : String -> FileContext -> FileContext
setSource str fc
  = { source       := Just str
    , start.source := Just str
    , end.source   := Just str
    } fc

namespace Ref

  export
  setSource : String -> Ref -> Ref
  setSource new ref = { span $= setSource new } ref

export
Show Location where
  show (MkLoc Nothing  l c) = with List concat [show l, ":", show c]
  show (MkLoc (Just n) l c) = with List concat [n, ":", show l, ":", show c]

export
Show FileContext where
  show (MkFC Nothing (MkLoc _ l scol) (MkLoc _ _ ecol)) = with List concat ["global:", show (S l), ":", show (S scol), "-", show (S ecol), ":"]
  show (MkFC (Just x) (MkLoc _ l scol) (MkLoc _ _ ecol)) = with List concat [x, ":", show (S l), ":", show (S scol), "-", show (S ecol), ":"]

-- [ EOF ]
