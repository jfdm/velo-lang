||| Stuff that goes wrong.
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Velo.Error

import Data.String

import System.File
import Toolkit.Data.Location
import Toolkit.System
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

import Toolkit.Options.ArgParse

import Velo.Types

import Velo.Lexer.Token


%default total

namespace Options
  public export
  data Error : Type where
    OError : ArgParseError -> Options.Error

namespace Lexing
  public export
  data Error : Type where
    LError : String -> LexFail -> Lexing.Error

namespace Parsing
  public export
  data Error : Type where
     PError : String -> ParseError (Token) -> Parsing.Error

namespace Elaborating
  public export
  data Error = Mismatch Ty Ty
             | NotBound String
             | FuncExpected Ty
             | Hole String
             | Err FileContext Elaborating.Error

namespace Evaluating
  public export
  data Error = OOF

namespace Velo

  public export
  data Error : Type where
    Internal : String -> Velo.Error
    Generic : String -> Velo.Error
    Opts    : Options.Error -> Velo.Error
    Lex     : Lexing.Error -> Velo.Error
    Parse   : Parsing.Error -> Velo.Error
    Elab : Elaborating.Error -> Velo.Error
    Eval : Evaluating.Error -> Velo.Error

-- [ EOF ]
