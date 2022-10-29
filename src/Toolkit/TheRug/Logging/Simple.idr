module Toolkit.TheRug.Logging.Simple

import Data.String
import Toolkit.TheRug
import public Toolkit.Logging.Simple

%default total

export
%inline
logWhen : (f               : LogLevel -> String)
       -> (given, expected : LogLevel)
       -> (msg             : String)
                          -> TheRug e ()
logWhen f g e msg
  = if (g <= e || g == FATAL || g == ALL)
     then putStrLn (unwords [(f g), msg])
     else pure ()

export
%inline
log : (f     : LogLevel -> String)
   -> (level : LogLevel)
   -> (msg   : String)
            -> TheRug e ()
log f l msg
  = putStrLn (unwords [(f l), msg])

namespace Default
  export
  log : (level : LogLevel)
     -> (msg   : String)
              -> TheRug e ()
  log = log (Default.toString)

  export
  logWhen : (given, expected : LogLevel)
         -> (msg             : String)
                            -> TheRug e ()
  logWhen = logWhen (Default.toString)

-- [ EOF ]
