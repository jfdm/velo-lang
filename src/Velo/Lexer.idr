|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Velo.Lexer

import public Data.List.Elem

import public Text.Lexer

import public Toolkit.Text.Lexer.Run

import public Velo.Lexer.Token

import Velo.Core

%default total

namespace Velo
  public export
  Symbols : List String
  Symbols = [ -- special composite symbols
              "->", "=>"
              -- Deliminators
            , "(", ")"

              -- Plain-old Symbols
            , ":"
            , "="
            ]


  public export
  Keywords : List String
  Keywords = [ "fun", "let", "in"

             -- CTors
             , "true", "false"
             , "zero", "inc"

             -- Operations
             , "and", "add"
             , "the"

             -- Types
             , "nat", "bool"
             ]


identifier : Lexer
identifier = pred startIdent <+> many (pred validIdent)
  where
    startIdent : Char -> Bool
    startIdent '_' = True
    startIdent x = isAlpha x

    validIdent : Char -> Bool
    validIdent '_' = True
    validIdent x = isAlphaNum x

namespace Velo

  tokenMap : TokenMap Velo.Token
  tokenMap = with List
    [
      (space, WS)
    , (lineComment (exact "--"), LineComment)
    , (blockComment (exact "{-") (exact "-}"), BlockComment)
    ]
    ++
       map (\x => (exact x, Symbol)) Symbols
    ++
    [
      (identifier, (\x => if elem x Keywords then Keyword x else ID x))
    , (any, NotRecognised)
    ]

  keep : WithBounds Velo.Token -> Bool
  keep (MkBounded t _ _) = case t of
      BlockComment _ => False
      LineComment  _ => False
      WS           _ => False
      _              => True




  public export
  IsKeyword : String -> Type
  IsKeyword s = Elem s Velo.Keywords

  public export
  IsSymbol : String -> Type
  IsSymbol s = Elem s Velo.Symbols

  export
  Lexer : Lexer Token
  Lexer = MkLexer (Lexer.Velo.tokenMap) keep EndInput

  export
  lexFile : String -> Velo (List (WithBounds Token))
  lexFile fname
    = do toks <- lexFile (\e => Lex (LError fname e))
                         Velo.Lexer
                         fname
         pure toks

-- [ EOF ]
