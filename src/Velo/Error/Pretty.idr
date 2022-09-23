module Velo.Error.Pretty

import Data.String
import Data.List1
import System.File
import Toolkit.Data.Location
import Toolkit.System
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run
import Toolkit.Options.ArgParse

import Text.Lexer

import Velo.Types
import Velo.Error
import Velo.Lexer.Token

-- @TODO Make error messages prettier.

%default total

Show Ty where
  show TyNat         = "NAT"
  show TyBool        = "BOOL"
  show (TyFunc x y)  = "(\{show x} -> \{show y}) "


Show (Lexing.Error) where
  show (LError _ e) = show e

Show (Options.Error) where
  show (OError err)
    = show err

Show (Parsing.Error) where
  show (PError _ err)
    = show err

Show (Evaluating.Error) where
  show OOF = "Out of Fuel"

Show (Elaborating.Error) where

  show (Err fc err)
    = unlines [show fc
              , show err]

  show (FuncExpected ty)
    = "Function expected, was given:\n\t\{show ty}"

  show (NotBound ref)
    = "Not a bound identifier:\n\t\{show ref}"

  show (Mismatch given expected)
    = unlines ["Type Mismatch:"
              , "  Given:"
              , "    \{show given}"
              , "  Expected:"
              , "    \{show expected}"
              ]

export
Show (Velo.Error) where
  show (Generic err)
    = show err

  show (Opts r)
    = "Option Error\n" ++ show r

  show (Lex x)
    = "Lexing Error\n" ++ show x

  show (Parse x)
    = "Parsing Error\n" ++ show x

  show (Elab x)
    = "Type Checking Error\n" ++ show x
  show (Eval x)
    = "Evaluation Error\n" ++ show x

-- [ EOF ]
