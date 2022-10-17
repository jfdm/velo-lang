||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Velo.Lexer.Token

import Text.Bounded

%default total

public export
data Identifier = MkIdentifier String

export
Eq Identifier where
  (==) (MkIdentifier x) (MkIdentifier y) = x == y

namespace Velo
  public export
  data Token = ID String
              | Keyword String
              | LineComment String
              | BlockComment String

              | Symbol String
              | WS String
              | NotRecognised String
              | EndInput

showToken : Show a => String -> a -> String
showToken n a
  = "(\{n} \{show a})"

export
Show Token where
  show (ID id)             = showToken "ID" id
  show (Keyword str)       = showToken "Keyword" str
  show (LineComment str)   = showToken "LineComment" str

  show (BlockComment str)  = showToken "BlockComment" str

  show (Symbol s) = showToken "Symbol" s
  show (WS ws) = "WS"
  show (NotRecognised s) = showToken "Urgh" s
  show EndInput          = "EndInput"

export
[veloWB] Show a => Show (WithBounds a) where
  show (MkBounded t _ _) = show t

export
[veloWBs] Show (List (WithBounds Token)) where
  show ts = show $ map (show @{veloWB} ) ts

export
Eq Token where
  (==) (ID x) (ID y) = x == y

  (==) (LineComment x) (LineComment y) = x == y
  (==) (Keyword x) (Keyword y) = x == y

  (==) (Symbol x) (Symbol y) = x == y

  (==) (WS x) (WS y) = x == y
  (==) (NotRecognised x) (NotRecognised y) = x == y
  (==) EndInput EndInput = True
  (==) _ _ = False


-- [ EOF ]
