module Main

import Velo.Core
import Velo.Options
import Velo.Pipeline
import Velo.REPL


covering
mainRug : Velo ()
mainRug
  = do opts <- getOpts

       when (repl opts) $ repl

       pipeline opts

covering
main : IO ()
main
  = do Velo.run mainRug


-- [ EOF ]
