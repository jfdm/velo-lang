module Velo.REPL

import Data.SnocList.Quantifiers
import Data.List.Quantifiers
import Data.String

import Velo.Types
import Velo.Values
import Velo.Semantics.Evaluation

import Velo.Core
import Velo.IR.Common
import Velo.IR.AST
import Velo.IR.Holey
import Velo.IR.Term
import Velo.Parser
import Velo.Lexer
import Velo.Elaborator.Holey
import Velo.Elaborator.Term
import Velo.Elaborator
import Velo.Eval
import Velo.Trace
import Velo.Options
import Velo.Commands

%default total


State : Type
State = ()

MkState : State
MkState = ()

todo : State -> Velo State
todo st = do putStrLn "Not Yet Implemented"
             pure st

process : State -> Cmd -> Velo State
process st Quit
  = do putStrLn "Quitting, Goodbye."
       exitSuccess

process st Help
  = do putStrLn helpStr
       pure st

process st Holes = todo st
process st (TypeOfHole str)
  = todo st

export covering
repl : Velo ()
repl
  = repl "Velo>" commands MkState process printLn



-- [ EOF ]
