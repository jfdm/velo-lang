||| The `LogLevel` type allows for simple logging in the style of the Log4j/Python family of
||| loggers.
module Toolkit.Logging.Simple


||| Logging levels are essentially natural numbers wrapped in a data type for
||| convenience.
|||
public export
data LogLevel : Type where
  ||| Log No Events
  OFF : LogLevel

  ||| A fine-grained debug message, typically capturing the flow through
  ||| the application.
  TRACE : LogLevel

  ||| A general debugging event.
  DEBUG : LogLevel

  |||  An event for informational purposes.
  INFO : LogLevel

  ||| An event that might possible lead to an error.
  WARN : LogLevel

  ||| An error in the application, possibly recoverable.
  ERROR : LogLevel

  ||| A severe error that will prevent the application from continuing.
  FATAL : LogLevel

  ||| All events should be logged.
  ALL : LogLevel

export
Eq LogLevel where
  (==) OFF   OFF   = True
  (==) TRACE TRACE = True
  (==) DEBUG DEBUG = True
  (==) INFO  INFO  = True
  (==) WARN  WARN  = True
  (==) ERROR ERROR = True
  (==) FATAL FATAL = True
  (==) ALL   ALL   = True
  (==) _     _     = False

Cast (LogLevel) Nat where
  cast OFF   = 0
  cast TRACE = 1
  cast DEBUG = 2
  cast INFO  = 3
  cast WARN  = 4
  cast ERROR = 5
  cast FATAL = 6
  cast ALL   = 7

export
Ord LogLevel where
  compare a b
    = compare (cast {to=Nat} a)
              (cast {to=Nat} b)

namespace Default
  export
  toString : LogLevel -> String
  toString OFF   = "[ OFF   ]"
  toString TRACE = "[ TRACE ]"
  toString DEBUG = "[ DEBUG ]"
  toString INFO  = "[ INFO  ]"
  toString WARN  = "[ WARN  ]"
  toString ERROR = "[ ERROR ]"
  toString FATAL = "[ FATAL ]"
  toString ALL   = "[ ALL   ]"

export
Show LogLevel where
  show = toString

-- [ EOF ]
