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


mainRug : Velo ()
mainRug
  = do opts <- getOpts

       fname <- embed
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

                 putStrLn "# Executing"
                 v <- eval tm

                 prettyComputation v
                 putStrLn "# Finished"

main : IO ()
main
  = do Velo.run mainRug
