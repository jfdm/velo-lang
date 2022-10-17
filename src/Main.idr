module Main

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

namespace Velo
  export
  pipeline : Opts -> Velo ()
  pipeline opts
    = do fname <- embed
                    (Generic "File expected.")
                    (file opts)

         when (justLex opts)
           $ do toks <- lexFile fname
                putStrLn (show @{veloWBs} toks)
                exitSuccess

         ast <- fromFile fname
         putStrLn "# Finished Parsing"

         res <- elab ast

         putStrLn "# Finished Type Checking"

         case res of
           HasHoles metas prf
             => do prettyMetas metas
                   exitSuccess

           ClosedTerm type tm ItIsEmpty
             => do when (justCheck opts)
                     $ exitSuccess

                   v <- eval tm
                   putStrLn "# Finished Executing"

                   prettyComputation v
                   putStrLn "# Finished"

  State : Type
  State = ()

  MkState : State
  MkState = ()

  export
  repl : Velo ()
  repl = repl "Velo>" commands MkState process printLn
    where
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



mainRug : Velo ()
mainRug
  = do opts <- getOpts

       when (repl opts) $ Velo.repl

       pipeline opts

main : IO ()
main
  = do Velo.run mainRug
