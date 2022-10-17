||| The Core Computation Context.
|||
||| Borrowed from Idris2 `Rug` is the core computation context that
||| brings the computations together.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.TheRug

import public System
import System.File
import System.Clock
import Data.Vect
import Data.String

import Decidable.Equality

import Text.Parser
import Text.Lexer


import Toolkit.System
import Toolkit.Text.Parser.Run
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run

import Toolkit.Options.ArgParse
import Toolkit.Commands

import Toolkit.Data.DList
import Toolkit.Decidable.Informative

%default total

||| Because it ties everything together.
export
record TheRug e t where
  constructor MkTheRug
  rugRun : IO (Either e t)

export
run : (whenErr : e -> IO b)
   -> (whenOK  : a -> IO b)
   -> (prog    : TheRug e a)
                   -> IO b
run whenErr whenOK (MkTheRug rugRun)
  = either whenErr
           whenOK
           !rugRun

export
%inline
fail : (msg : e)
           -> TheRug e a
fail e
  = MkTheRug (pure (Left e))

export
%inline
throw : (msg : e) -> TheRug e a
throw = fail

export
Functor (TheRug e) where
  map f (MkTheRug a)
    = MkTheRug (map f <$> a)

export
%inline
bind : TheRug       e a
     -> (a -> TheRug e b)
     -> TheRug e b
bind (MkTheRug act) f
  = MkTheRug (act >>=
             (\res =>
                case res of
                  Left  err => pure (Left err)
                  Right val => rugRun (f val)))

export
Applicative (TheRug e) where
  pure a = MkTheRug (pure (pure a))
  mf <*> mx = bind mf (<$> mx)

export
Monad (TheRug e) where
  (>>=) = bind

export
%inline
during : (e -> e')
       -> TheRug e a
       -> TheRug e' a
during f (MkTheRug a)
  = MkTheRug (mapFst f <$> a)

export
HasIO (TheRug e) where
  liftIO op = MkTheRug $
    do o <- op
       pure (Right o)

%inline
export
embed : IO a -> TheRug e a
embed = liftIO

export
%inline
embed_ : (this : IO        a)
              -> TheRug e ()
embed_ this = ignore (embed this)

export
%inline
(<|>) : TheRug e a
     -> Lazy (TheRug e a)
     -> TheRug e a
(<|>) (MkTheRug first) backup
  = MkTheRug (do res <- first
                 case res of
                   (Left _)    => rugRun backup
                   (Right val) => pure (Right val))

export
%inline
tryCatch : (prog  : TheRug ea a)
        -> (onErr : ea -> TheRug ea a)
                 -> TheRug ea a
tryCatch (MkTheRug this) onErr
  = MkTheRug (do res <- this
                 either (rugRun . onErr)
                        (pure   . Right)
                        res
                   )

export
%inline
handleWith : Show ea => (when : ea -> Maybe ea)
          -> (prog :       TheRug ea a)
          -> (next : Lazy (TheRug ea a))
                  ->       TheRug ea a
handleWith when prog next
  = tryCatch prog
             (\err => maybe next
                            throw
                            (when err)
             )

namespace Maybe
  export
  %inline
  embed : (err : b)
       -> (result : Maybe a)
                 -> TheRug b a
  embed _ (Just x)
    = pure x

  embed err Nothing
    = throw err

namespace Either
  export
  %inline
  embed : (f      : e -> b)
       -> (result : Either e r)
                 -> TheRug b r
  embed _ (Right val)
    = pure val

  embed f (Left err)
    = throw (f err)

namespace Decidable
  export
  %inline
  embed : (err : b)
       -> (result : Dec      r)
                 -> TheRug b r
  embed _ (Yes prfWhy)
    = pure prfWhy

  embed err (No prfWhyNot)
    = throw err

  export
  %inline
  when : (result : Dec      a)
      -> (this   : Lazy (TheRug e ()))
                   -> TheRug e ()
  when (Yes _) this
    = this
  when (No _) _
    = pure ()

  export
  %inline
  whenNot : (result : Dec      r)
         -> (this   : Lazy (TheRug e ()))
                   -> TheRug e ()
  whenNot (Yes _) _
    = pure ()
  whenNot (No _) this
    = this

  namespace Informative
    export
    %inline
    embed : (f : a -> b)
         -> (result : DecInfo a r)
                   -> TheRug  b r
    embed f (Yes prfWhy)
      = pure prfWhy

    embed f (No msgWhyNot prfWhyNot)
      = throw (f msgWhyNot)

namespace Traverse

  namespace List

    traverse' : (acc : List b)
             -> (f   : a -> TheRug e b)
             -> (xs  : List a)

                    -> TheRug e (List b)
    traverse' acc f []
      = pure (reverse acc)

    traverse' acc f (x :: xs)
      = traverse' (!(f x) :: acc) f xs

    export
    %inline
    traverse : (f  : a -> TheRug e b)
            -> (xs : List a)
                  -> TheRug e (List b)
    traverse = traverse' Nil

  namespace Vect
    export
    %inline
    traverse : (f  : a -> TheRug e b)
            -> (xs : Vect n a)
                  -> TheRug e (Vect n b)
    traverse f []
      = pure Nil

    traverse f (x :: xs)
      = [| f x :: traverse f xs |]

namespace IO

  export
  covering -- not my fault
  readFile : (onErr : String -> FileError -> e)
          -> (fname : String)
                   -> TheRug e String
  readFile onErr fname
    = do Right content <- (TheRug.embed (readFile fname))
           | Left err => throw (onErr fname err)
         pure content
  export
  parseArgs : (f    : ArgParseError -> e)
           -> (def  : opts)
           -> (conv : Arg -> opts -> Maybe opts)
                   -> TheRug e opts
  parseArgs f def c
    = do args <- embed getArgs
         case parseArgs def c args of
           Left err => throw (f err)
           Right o  => pure o

namespace Lexing
  export
  covering -- not my fault
  lexFile : (onErr : LexFail -> err)
         -> (lexer : Lexer a)
         -> (fname : String)
                  -> TheRug err
                            (List (WithBounds a))
  lexFile onErr lexer fname
    = do Right toks <- TheRug.embed (lexFile lexer fname)
           | Left err => throw (onErr err)
         pure toks

namespace Parsing
  export
  covering -- not my fault
  parseFile : {e     : _}
           -> (onErr : ParseError a -> err)
           -> (lexer : Lexer a)
           -> (rule  : Grammar () a e ty)
           -> (fname : String)
                    -> TheRug err ty
  parseFile onErr lexer rule fname
      = do Right res <- TheRug.embed (parseFile lexer rule fname)
                 | Left err => throw (onErr err)
           pure res

  export
  parseString : {e     : _}
             -> (onErr : ParseError a -> err)
             -> (lexer : Lexer a)
             -> (rule  : Grammar () a e ty)
             -> (fname : String)
                      -> TheRug err ty
  parseString onErr lexer rule str
      = case parseString lexer rule str of
          Left err => throw (onErr err)
          Right str => pure str

namespace Cheap
  export
  %inline
  log : (msg      : String)
                 -> TheRug e ()
  log = putStrLn


  namespace Timed
    export
    %inline
    log : (showTime : Bool)
       -> (time     : Lazy (Clock type))
       -> (msg      : String)
                   -> TheRug e ()
    log showTime t m
      = if showTime
        then do print t
                putStrLn m
        else putStrLn m

    export
    %inline
    try : Show e
       => (showTime : Bool)
       -> (msg      : String)
       -> (f        : a -> TheRug e b)
       -> (val      : a)
                   -> TheRug e b
    try showTime msg f val
      = do start <- (embed $ clockTime UTC)
           res   <- embed  (run (\err => do stop <- clockTime UTC
                                            putStrLn "Error Happened"
                                            let d = timeDifference stop start
                                            if showTime
                                              then do putStrLn (unwords [msg, show d])
                                                      printLn err
                                                      exitFailure
                                              else do putStrLn msg
                                                      printLn err
                                                      exitFailure)
                                (\res => do stop <- clockTime UTC
                                            let d = timeDifference stop start
                                            if showTime
                                              then do putStrLn (unwords [msg, show d])
                                                      pure res
                                              else do putStrLn msg
                                                      pure res)

                                (f val))
           pure res

namespace REPL
  ||| Adapted from `System.REPL`
  |||
  ||| We assume that `onInput` exits cleanly...
  covering export
  repl : (prompt  : String)
      -> (state   : a)
      -> (onInput : (state : a)
                 -> (str   : String)
                          -> TheRug e a)
                 -> TheRug e ()
  repl prompt state onInput
    = do eof <- fEOF stdin
         if eof
           then pure ()
           else do putStr prompt
                   putStr " " -- intentional
                   fflush stdout

                   str <- getLine
                   new_state <- onInput state str

                   repl prompt new_state onInput

  namespace Command

    covering export
    repl : (prompt  : String)
        -> (cmds    : Commands c)
        -> (state   : a)
        -> (onInput : (state : a)
                   -> (str   : c)
                            -> TheRug e a)
        -> (onErr : Commands.Error -> TheRug e ())
                   -> TheRug e ()
    repl prompt cmds state onInput onErr
      = do eof <- fEOF stdin
           if eof
             then pure ()
             else do putStr prompt
                     putStr " " -- intentional
                     fflush stdout

                     str <- getLine

                     case processCommand cmds str of
                       Left err => do onErr err
                                      repl prompt cmds state onInput onErr
                       Right cmd
                         => do nst <- onInput state cmd
                               repl prompt cmds nst onInput onErr


-- [ EOF ]
