module Main

import Data.String

import Velo.Types
import Velo.Terms
import Velo.Values
import Velo.Semantics.Evaluation

import Velo.Core
import Velo.IR.AST
import Velo.IR.Holey
import Velo.IR.Term
import Velo.Parser
import Velo.Lexer
import Velo.Elaborator.Holey
import Velo.Elaborator.Term
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

       (ty ** holes ** t) <- synth [] ast
       let (metas ** inv) = initInvariant [] [] holes
       let t = wscoped t inv
       putStrLn "# Finished Type Checking"

       case metas of
         (_ :: _) => do prettyMetas metas
                        exitSuccess
         []
           => do when (justCheck opts)
                   $ exitSuccess

                 putStrLn "# Executing"
                 v <- eval t
                 prettyComputation v
                 putStrLn "# Finished"

main : IO ()
main
  = do Velo.run mainRug
