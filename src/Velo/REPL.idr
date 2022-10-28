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
import Velo.Elaborator.Instantiate
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
  file : Maybe (SynthResult [<])

defState : State
defState = MkSt Nothing

todo : State -> Velo State
todo st = do putStrLn "Not Yet Implemented"
             pure st

onFile : (st : State )
      -> (f  : SynthResult [<] -> Velo State)
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
           (\case MkSynthResult [] _
                    => do putStrLn "No Holes"
                          pure st
                  MkSynthResult ms _
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
  = onHoles st $ \ms => do
      let Just (m ** _) = getByName str ms
        | _ => st <$ putStrLn "\{str} is not a valid hole."
      printLn (pretty {ann = ()} m)
      pure st

process st (Instantiate hole term)
  = onFile st $ \ (MkSynthResult ms tm) => do
      let Just (MkMeta nm scp ty ** p) = getByName hole ms
        | Nothing => st <$ putStrLn "\{hole} is not a valid hole"

      ast <- fromString term
      MkCheckResult [] res <- elab scp ty ast
        | _ => st <$ putStrLn "\{term} is not hole-free"

      let tm = instantiate tm p (embed res)
      printLn (pretty {ann = ()} (unelaborate tm))
      pure ({ file := Just (MkSynthResult _ tm) } st)

process st Eval
  = onFile st
           (\(MkSynthResult ms tm)
                => do v <- eval tm
                      prettyComputation v
                      pure st)

process st CSE
  = onFile st
           (\(MkSynthResult ms tm)
                => do let tm = cse tm
                      printLn (pretty {ann = ()} (unelaborate tm))
                      pure st)

process st ConstantFolding
  = onFile st
           (\(MkSynthResult ms tm)
                => do let tm = cfold tm
                      printLn (pretty {ann = ()} (unelaborate tm))
                      pure st)

process st (Load str)
  = tryCatch (do ast <- fromFile str
                 putStrLn "# Finished Parsing"
                 res <- elab [<] ast
                 putStrLn "# Finished Type-Checking"
                 pure ({ file := Just res} st)
                 )
             (\err => do printLn err
                         pure st)

process st Show
  = onFile st
           (\(MkSynthResult ms tm)
                => do printLn (pretty {ann = ()} (unelaborate tm))
                      pure st)


export covering
repl : Velo ()
repl
  = repl "Velo>" commands defState process printLn



-- [ EOF ]
