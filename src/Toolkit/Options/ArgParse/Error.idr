|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Options.ArgParse.Error

import Data.String

import System.File

import Toolkit.Data.Location

import Toolkit.Options.ArgParse.Model
import Toolkit.Options.ArgParse.Lexer
import Toolkit.Options.ArgParse.Parser

%default total

public export
data ArgParseError : Type where
  InvalidOption   : Arg -> ArgParseError
  MalformedOption : ParseError Token -> ArgParseError

export
(Show Arg) => Show ArgParseError where
  show (InvalidOption o)
    = "Invalid Option " ++ show o
  show (MalformedOption err)
    = "Malformed Option " ++ show err


-- --------------------------------------------------------------------- [ EOF ]
