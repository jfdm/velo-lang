|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.System

import System

%default total

export
tryOrDie : Show err
        => Either err type
        -> IO type
tryOrDie (Left err) =
  do putStrLn "Error Happened"
     printLn err
     exitFailure
tryOrDie (Right res) = pure res

-- [ EOF ]
