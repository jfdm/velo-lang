|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Options.ArgParse.Lexer

import Data.String
import Text.Lexer


import public Toolkit.Text.Lexer.Run

%default total

public export
data Token = SFlag   String
           | LFlag   String
           | Equals String
           | Quoted String
           | WS String
           | Arg String
           | Unknown String
           | EndInput

export
Show Token where
  show (LFlag    x) = unwords ["LFlag",   show x]
  show (SFlag    x) = unwords ["SFlag",   show x]
  show (Equals   x) = unwords ["Equals", show x]
  show (Quoted  x) = unwords ["Quoted", show x]
  show (WS      x) = unwords ["WS",     show x]
  show (Arg    x) = unwords ["Arg",     show x]
  show (Unknown x) = unwords ["BAD TOKEN", show x]
  show EndInput = "ENDINPUT"

ch : Lexer
ch = pred (isAlphaNum)

str : Lexer
str = some (pred isAlphaNum)

shortFlag : Lexer
shortFlag = is '-' <+> ch

longFlag : Lexer
longFlag = is '-' <+> is '-' <+> str

equals : Lexer
equals = is '='

arg : Lexer
arg = any <+> manyUntil space any

rawTokens : TokenMap Token
rawTokens =
  [ (space, WS)
  , (stringLit, Quoted)
  , (longFlag, LFlag)
  , (shortFlag, SFlag)
  , (equals, Equals)
  , (arg, Arg)
  , (symbol, Unknown)
  ]

keep : WithBounds Token -> Bool
keep (MkBounded t _ _) with (t)
  keep (MkBounded t _ _) | (WS x) = False
  keep (MkBounded t _ _) | _      = True

export
ArgParseLexer : Lexer Token
ArgParseLexer = MkLexer rawTokens keep EndInput

export
lexArgParseStr : String -> Either LexError (List (WithBounds Token))
lexArgParseStr = lexString ArgParseLexer

export
lexArgParseFile : String -> IO $ Either LexFail (List (WithBounds Token))
lexArgParseFile = lexFile ArgParseLexer

-- --------------------------------------------------------------------- [ EOF ]
