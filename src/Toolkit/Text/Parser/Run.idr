|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Text.Parser.Run

import System.File

import Text.Parser
import Text.Lexer

import Data.List1
import Data.String
import Toolkit.Data.Nat
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run

import Toolkit.Text.Parser.Support


%default total

public export
record ParseFailure a where
  constructor MkParseFail
  error    : String
  location : FileContext

public export
data ParseError a = PError (List1 (ParseFailure a))
                  | LError LexError
                  | FError FileError


export
Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

export
Show a => Show (Run.ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map show err))

  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]


convert : (src : Maybe String)
       -> (err : ParsingError a)
              -> ParseFailure a
convert src (Error msg Nothing)
  = MkParseFail msg (record {source = src} emptyFC)

convert src (Error msg (Just loc))
  = let s = startBounds loc in
    let e = endBounds   loc in
    let fc = if s == e
             then newFC src s (mapSnd (+1) e)
             else newFC src s e
    in MkParseFail msg fc

runConvert : Maybe String
          -> List1 (ParsingError a)
          -> ParseError a
runConvert src es = PError (map (convert src) es)

export
parseString : {e     : _}
           -> (lexer : Lexer a)
           -> (rule  : Grammar () (a) e ty)
           -> (str   : String)
                   -> (Either (ParseError a) ty)
parseString lexer rule str =
  case lexString lexer str of
    Left err   => Left (LError err)
    Right toks =>
      case parse rule toks of
        Left err      => Left (runConvert Nothing err)
        Right (val,_) => Right val

export
covering
parseFile : {e     : _}
         -> (lexer : Lexer a)
         -> (rule  : Grammar () a e ty)
         -> (fname : String)
         -> IO $ Either (ParseError a) ty
parseFile lexer grammar fname =
  case !(lexFile lexer fname) of
    Left (LError err) => pure (Left (LError err))
    Left (LIOErr err) => pure (Left (FError err))
    Right toks =>
      case parse grammar toks of
        Left err      => pure (Left (runConvert (Just fname) err))
        Right (val,_) => pure (Right val)

-- [ EOF ]
