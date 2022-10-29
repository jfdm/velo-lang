module Velo.Pipeline

import Data.SnocList.Quantifiers
import Data.List.Quantifiers
import Data.String

import Velo.Types
import Velo.Values

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

export
pipeline : Opts -> Velo ()
pipeline opts
  = do fname <- embed
                  (Generic "File expected.")
                  (file opts)

       let level = if justCheck opts
                     then OFF
                     else ALL


       when (justLex opts)
         $ do toks <- lexFile fname
              putStrLn (show @{veloWBs} toks)
              exitSuccess

       ast <- fromFile fname
       logWhen INFO level "# Finished Parsing"

       res <- elab [<] ast

       logWhen INFO level "# Finished Type Checking"

       unless (null res.metas) $
         prettyMetas res.metas

       when (justCheck opts)
         $ exitSuccess

       v <- eval res.term
       log INFO "# Finished Executing"

       prettyComputation v
       log INFO "# Finished"

-- [ EOF ]
