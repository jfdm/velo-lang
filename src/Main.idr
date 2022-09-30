module Main

import Data.String

import Velo.Types
import Velo.Terms
import Velo.Values
import Velo.Semantics.Evaluation

import Velo.Core
import Velo.IR.AST
import Velo.Parser
import Velo.Lexer
import Velo.Elaborator
import Velo.Eval
import Velo.Trace
import Velo.Options

showToks : (List (WithBounds Token)) -> List String
showToks = map (\(MkBounded t _ _) => show t)

mainRug : Velo ()
mainRug
  = do opts <- getOpts

       fname <- embed
                  (Generic "File expected.")
                  (file opts)

       when (justLex opts)
         $ do toks <- lexFile fname
              putStrLn $ unwords (showToks toks)
              exitSuccess

       ast <- fromFile fname
       putStrLn "# Finished Parsing"

       res <- elab ast
       putStrLn "# Finished Type Checking"

       case res of
         Holly h => do prettyHoles h
                       exitSuccess
         Closed tm
           => do when (justCheck opts)
                   $ exitSuccess

                 putStrLn "# Executing"
                 v <- eval tm
                 prettyComputation v
                 putStrLn "# Finished"
                 pure ()

main : IO ()
main
  = do Velo.run mainRug
