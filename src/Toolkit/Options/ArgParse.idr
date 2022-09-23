|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Options.ArgParse

import Data.List
import Data.String

import        Toolkit.Options.ArgParse.Lexer
import        Toolkit.Options.ArgParse.Parser

import public Toolkit.Options.ArgParse.Model

import        Toolkit.Options.ArgParse.Parser
import public Toolkit.Options.ArgParse.Error

%default total
-- ----------------------------------------------------------------- [ Records ]

private
convOpts : (Arg -> a -> Maybe a)
        -> a
        -> List Arg
        -> Either ArgParseError a
convOpts  _   o Nil       = pure o
convOpts conv o (x :: xs) = case conv x o of
    Nothing => Left (InvalidOption x)
    Just o' => do
      os <- convOpts conv o' xs
      pure os

||| Parse arguments using a record.
|||
||| @orig The starting value of the record representing the options.
||| @conv A user supplied conversion function used to update the record.
||| @args The *unmodified* result of calling `System.getArgs` or `Effects.System.geArgs`.
export
parseArgs : (orig : a)
         -> (conv : Arg -> a -> Maybe a)
         -> (args : List String)
         -> Either ArgParseError a
parseArgs o _    Nil     = pure o
parseArgs o _    [a]     = pure o
parseArgs o func (a::as) = do
    case parseArgsStr (unwords as) of
      Left err  => Left (MalformedOption err)
      Right res => do
        r <- convOpts func o res
        pure r

-- --------------------------------------------------------------------- [ EOF ]
