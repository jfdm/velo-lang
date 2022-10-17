|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Text.Lexer.Run

import System.File

import Data.List
import Data.String

import Text.Lexer

import Toolkit.Data.Nat
import Toolkit.Data.Location

%default total



public export
record LexError where
  constructor MkLexFail
  location : Location
  input  : String

public export
data LexFail = LError LexError | LIOErr FileError

export
Show LexFail where
  show (LError (MkLexFail loc i)) =
    unwords ["Lexing Error at ", show loc, ":\n", show i]
  show (LIOErr err) =
    unwords ["FileError", show err]

public export
record Lexer a where
  constructor MkLexer
  tokenMap : TokenMap a
  keep : WithBounds a -> Bool
  endInput : a

export
lexString : Lexer a
         -> String
         -> Either LexError (List (WithBounds a))
lexString lexer str =
      case Lexer.Core.lex (tokenMap lexer) str of
        (tok, (c,l, "")) =>
          Right $ (filter (keep lexer) tok ++ [MkBounded (endInput lexer) False (MkBounds l c l c)])

        (_,   (c,l,i))    => Left (MkLexFail (MkLoc Nothing (toNat c) (toNat l)) i)

export covering
lexFile : Lexer a -> String -> IO $ Either LexFail (List (WithBounds a))
lexFile lexer fname = do
  Right str <- readFile fname | Left err => pure (Left (LIOErr err))
  case lexString lexer str of
        Left err => pure $ Left (LError ({ location->source := Just fname } err))
        Right toks => pure (Right toks)

-- [ EOF ]
