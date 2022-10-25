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

onFile : (st : State )
      -> (f  : ElabResult -> Velo State)
            -> Velo State
onFile st f
  = maybe (do putStrLn "Need to load a file."
              pure st)
          f
          (file st)

onHoles : (st : State)
       -> (f  : List Meta -> Velo State)
             -> Velo State
onHoles st f
  = onFile st
           (\case MkElabResult [] _
                    => do putStrLn "No Holes"
                          pure st
                  MkElabResult ms _
                    => f ms)

process : State -> Cmd -> Velo State
process st Quit
  = do putStrLn "Quitting, Goodbye."
       exitSuccess

process st Help
  = do putStrLn helpStr
       pure st

process st Holes
  = onHoles st
            (\ms => do prettyMetas ms
                       pure st)

process st (TypeOfHole str)
  = onHoles st
            (\ms => do let m = getByName str ms
                       printLn (pretty {ann = ()} m)
                       pure st)

process st Eval
  = onFile st
           (\(MkElabResult ms tm)
                => do v <- eval tm
                      prettyComputation v
                      pure st)

process st CSE
  = onFile st
           (\(MkElabResult ms tm)
                => do let tm = cse tm
                      printLn (pretty {ann = ()} (unelaborate tm))
                      pure st)

process st ConstantFolding
  = onFile st
           (\(MkElabResult ms tm)
                => do let tm = cfold tm
                      printLn (pretty {ann = ()} (unelaborate tm))
                      pure st)

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
  = onFile st
           (\(MkElabResult ms tm)
                => do printLn (pretty {ann = ()} (unelaborate tm))
                      pure st)


export covering
repl : Velo ()
repl
  = repl "Velo>" commands defState process printLn



-- [ EOF ]
