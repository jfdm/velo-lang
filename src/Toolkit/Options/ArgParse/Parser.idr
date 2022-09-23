||| A simple parser for command options.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Options.ArgParse.Parser

import Text.Lexer
import Text.Parser

import Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Run

import Toolkit.Options.ArgParse.Lexer
import Toolkit.Options.ArgParse.Parser.API
import Toolkit.Options.ArgParse.Model

-- ----------------------------------------------------------------- [ Parsers ]

flagLong : Rule Arg
flagLong = do
  l <- longFlag
  pure $ Flag l

flagShort : Rule Arg
flagShort = do
   s <- shortFlag
   pure $ Flag s

kvLong : Rule Arg
kvLong = do
    key <- longFlag
    equals
    value <- (arg <|> quoted)
    pure $ KeyValue key value

kvShort : Rule Arg
kvShort = do
    k <- shortFlag
    v <- (arg <|> quoted)
    pure $ KeyValue k v

options : Rule Arg
options = kvShort <|> kvLong <|> flagShort <|> flagLong <|> (do fs <- arg; pure $ File fs)

args : RuleEmpty (List Arg)
args = do
    os <- many options
    pure $ os

export
parseArgsStr : (str  : String)
            -> Either (Run.ParseError Token) (List Arg)
parseArgsStr str = parseString ArgParseLexer args str

export
parseArgsFile :(fname : String)
            -> IO (Either (Run.ParseError Token) (List Arg))
parseArgsFile fn = parseFile ArgParseLexer args fn

-- --------------------------------------------------------------------- [ EOF ]
