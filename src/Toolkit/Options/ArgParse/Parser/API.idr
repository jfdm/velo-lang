|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Options.ArgParse.Parser.API

import Data.List
import Data.String

import Text.Token
import Text.Lexer
import Text.Parser

import Toolkit.Options.ArgParse.Lexer
import public Toolkit.Text.Parser.Support


%default total

namespace ArgParse
  public export
  Rule : Type -> Type
  Rule = Rule Unit Token

  public export
  RuleEmpty : Type -> Type
  RuleEmpty = RuleEmpty Unit Token

-- Some basic parsers used by all the intermediate forms

export
shortFlag : Rule String
shortFlag
    = terminal "Expected Short Flag"
               (\x => case x of
                           SFlag f => Just (substr 1 (length f) f)
                           _     => Nothing)

export
longFlag : Rule String
longFlag
    = terminal "Expected long flag"
               (\x => case x of
                           LFlag f => Just (substr 2 (length f) f)
                           _       => Nothing)

export
arg : Rule String
arg = terminal "Expected arg."
  (\x => case x of
           Arg s => Just (trim s)
           _     => Nothing)

export
equals : Rule ()
equals = terminal "Expected equals"
  (\x => case x of
           Equals _ => Just ()
           _        => Nothing)

export
quoted : Rule String
quoted = terminal "Expected quoted input"
    (\x => case x of
             Quoted s => Just $ rmQuotes s
             _        => Nothing)
  where
    rmQuotes : String -> String
    rmQuotes xs = pack $ filter (not . (==) '"') (unpack xs)

-- --------------------------------------------------------------------- [ EOF ]
