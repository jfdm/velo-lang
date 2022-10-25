module Velo.REPL

import Data.SnocList.Quantifiers
import Data.List.Quantifiers
import Data.String

import Velo.Types
import Velo.Values


import Velo.Error.Pretty
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
import Velo.Unelaboration
import Velo.Eval
import Velo.Pass.CSE
import Velo.Pass.Folding
import Velo.Trace
import Velo.Options
import Velo.Commands

%default total


record State where
  constructor MkSt
  file : Maybe ElabResult

defState : State
defState = MkSt Nothing

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

process st Holes
  = case (file st) of

      Just (MkElabResult [] _)
        => do putStrLn "No holes"
              pure st

      Just (MkElabResult ms _)
        => do prettyMetas ms
              pure st
      Nothing
        => do putStrLn "Need to load a file."
              pure st

process st (TypeOfHole str)
  = case (file st) of

      Just (MkElabResult [] _)
        => do putStrLn "No holes"
              pure st

      Just (MkElabResult ms _)
        => do let m = getByName str ms
              printLn (pretty {ann = ()} m)
              pure st
      Nothing
        => do putStrLn "Need to load a file."
              pure st

process st Eval
  = case file st of
      Just (MkElabResult ms tm)
        => do v <- eval tm
              prettyComputation v
              pure st

      Nothing
        => do putStrLn "Need to load a file."
              pure st

process st CSE
  = case file st of
      Just (MkElabResult ms tm)
        => do let tm = cse tm
              printLn (pretty {ann = ()} (unelaborate tm))
              pure st

      Nothing
        => do putStrLn "Need to load a file."
              pure st

process st ConstantFolding
  = case file st of
      Just (MkElabResult ms tm)
        => do let tm = cfold tm
              printLn (pretty {ann = ()} (unelaborate tm))
              pure st

      Nothing
        => do putStrLn "Need to load a file."
              pure st

process st (Load str)
  = tryCatch (do ast <- fromFile str
                 putStrLn "# Finished Parsing"
                 res <- elab ast
                 putStrLn "# Finished Type-Checking"
                 pure ({ file := Just res} st)
                 )
             (\err => do printLn err
                         pure st)

process st Show
  = case file st of
      Just (MkElabResult ms tm)
        => do printLn (pretty {ann = ()} (unelaborate tm))
              pure st

      Nothing
        => do putStrLn "Need to load a file."
              pure st
export covering
repl : Velo ()
repl
  = repl "Velo>" commands defState process printLn



-- [ EOF ]
