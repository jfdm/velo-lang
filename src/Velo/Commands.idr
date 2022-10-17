module Velo.Commands

import Text.Bounded
import Data.Either
import Data.String
import Data.Maybe

import public Toolkit.Commands

import Velo.Core

%default total

public export
data Cmd = Quit
         | Help
         | Holes
         | TypeOfHole String

export
commands : Commands Cmd
commands
  = setCommands
    [
      newCommand (names ["q", "quit", "exit"])
                 Quit
                 "Exit the REPL."

    , newCommand (names ["?", "h", "help"])
                 Help
                 "Show the list of available commands."

    , newCommand (names ["holes"])
                 Holes
                 "Show the current list of holes."

    , newCommand (names ["hole_type", "t"])
                 (options [REQ "name"])
                 TypeOfHole
                 "Show the specified hole."
    ]

export
Show OptDesc where
  show (REQ str) = "[\{str}]"
  show (OPT str str1) = "<\{str1}> [DEFAULT \{str}]"

export
Show Commands.Error where
  show ExpectedOption = "Option Expected"
  show (ArgsEmpty cds) = "There are more arguments required.\n\t:\{show $ map (\(MkBounded t l w) => show t) cds}"
  show (ToksExpected xs) = "Missing arguments:\n\t \{show xs}"
  show (WrongName strs) = "The name must be one of:\n\t \{show strs}"
  show IsVoid = "Missing colon and/or argument name."
  show ColonExpected = "Commands begin with a colon."
  show NameExpected = "A command was expected."
  show (ArgsExpected xs) = "The following arguments were expected:\n\t \{show xs}"
  show UnRecognised = "Not a recognised command."
  show (LError x) = "Malformed input."

show : CommandDesc a -> String
show cmd
    = unlines [unwords ["[\{concat $ intersperse "," (forget $ name cmd)}]"
                       , maybe "" (unwords . map show . forget) (argsDesc cmd)
                       ]
              , "\t" <+> maybe "" id (help cmd)
              ]

export
helpStr : String
helpStr
  = unlines (map show (forget commands))

-- [ EOF ]
