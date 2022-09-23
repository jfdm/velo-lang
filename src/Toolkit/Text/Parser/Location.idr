|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Text.Parser.Location

import Text.Lexer
import Text.Parser

import Toolkit.Data.Nat
import Toolkit.Data.Location
import Toolkit.Text.Parser.Support

%default total

namespace Toolkit
  export
  location : RuleEmpty state tok Location
  location = do
    (x,y) <- Text.Parser.location
    pure (MkLoc Nothing (toNat x) (toNat y))

  namespace WithFileName
    export
    location : String -> RuleEmpty state tok Location
    location fname = do
      l <- Toolkit.location
      pure (record { source = Just fname} l)

-- [ EOF ]
