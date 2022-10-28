||| Inspired by Idris2's `CommandLine`
module Toolkit.Commands

import Decidable.Equality
import Toolkit.Decidable.Informative

import public Data.List
import        Data.List.Quantifiers
import public Data.List1
import        Data.Maybe
import        Data.String
import        Text.Lexer
import        Text.Parser

import Toolkit.Data.List.Thinning

import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Support
import Toolkit.Text.Parser.Run

-- ## Definitions

public export
data OptDesc : Bool -> Type where
  REQ : String -> OptDesc b
  OPT : String -> String -> OptDesc b
  REST : String -> OptDesc False

namespace OptDescs

  public export
  data OptDescs : Bool -> Type where
    (::) : {b : Bool} -> OptDesc b -> OptDescs b -> OptDescs True
    Nil : OptDescs False

public export
options : OptDescs True -> OptDescs True
options = id

namespace All

  public export
  data All : (p : forall b. OptDesc b -> Type) -> OptDescs b -> Type where
    (::) : {0 p : forall b. OptDesc b -> Type} ->
           p o -> Commands.All.All p opts -> All p (o :: opts)
    Nil  : {0 p : forall b. OptDesc b -> Type} ->
           All p []

public export
BuildArg : OptDesc b -> Type
BuildArg (REQ str) = String
BuildArg (OPT _ str) = String
BuildArg (REST str) = String

public export
BuildArgs : (a : Type) -> OptDescs b -> Type
BuildArgs a [] = a
BuildArgs a (x :: xs) = BuildArg x -> BuildArgs a xs

public export
record CommandDesc (a : Type) where
  constructor MkCDesc
  name      : List1 String
  {nonEmpty : Bool}
  argsDesc  : OptDescs nonEmpty
  argsBuild : BuildArgs a argsDesc
  help      : Maybe String

-- ## Factories

export
names : (xs       : List String)
     -> {auto prf : NonEmpty xs}
                -> List1 String
names (x::xs) {prf = IsNonEmpty} = x ::: xs

namespace Enum
  export
  newCommand : List1 String -> a -> String -> CommandDesc a
  newCommand ns f mhelp = MkCDesc ns [] f (Just mhelp)

  export
  newCommandNoHelp : List1 String -> a -> CommandDesc a
  newCommandNoHelp ns f = MkCDesc ns [] f Nothing

export
newCommand : List1 String
          -> (desc : OptDescs True)
          -> BuildArgs a desc
          -> String
          -> CommandDesc a
newCommand ns desc f mstr
  = MkCDesc ns desc f (Just mstr)

export
newCommandNoHelp : List1 String
                -> (desc : OptDescs True)
                -> BuildArgs a desc
                -> CommandDesc a
newCommandNoHelp ns desc f
  = MkCDesc ns desc f Nothing

public export
Commands : Type -> Type
Commands a = List1 (CommandDesc a)

export
setCommands : (xs       : List (CommandDesc a))
        -> {auto prf : NonEmpty xs}
                    -> Commands a
setCommands (x :: xs) {prf = IsNonEmpty} = x ::: xs

-- ## Lexer

name : List String -> Lexer
name strs = choice (map exact strs)

export
data Token = NotRecognised String
           | WS String
           | CmdTok String
           | EndInput
           | Colon

showTok : String -> String -> String
showTok k v = "(\{k} \{v})"

export
Show Token where
  show EndInput = "EOI"
  show Colon = "Colon"
  show (NotRecognised str)
    = showTok "NotRecognised" (show str)
  show (WS str)
    = showTok "Space" (show str)
  show (CmdTok str)
    = showTok "CmdTok" (show str)

export
Eq Token where
  (==) (NotRecognised a) (NotRecognised b) = (==) a b
  (==) (WS a) (WS b) = (==) a b
  (==) (CmdTok a) (CmdTok b) = (==) a b
  (==) EndInput EndInput = True
  (==) Colon Colon = True
  (==) _ _ = False

tokenMap : TokenMap Commands.Token
tokenMap
  = with List [ (space, WS)
              , (is ':', const Colon)
              , (someUntil space any, CmdTok)
              , (any, NotRecognised)
              ]

keep : WithBounds Token -> Bool
keep (MkBounded t _ _) = case t of
    WS           _ => False
    _              => True


Lexer : Lexer Token
Lexer = MkLexer Commands.tokenMap keep EndInput

-- ## Processor

-- ### Errors

public export
data Error = ExpectedOption
           | ArgsEmpty (List (WithBounds Token))
           | ToksExpected (OptDescs True)
           | WrongName (List String)
           | IsVoid
           | ColonExpected
           | NameExpected
           | ArgsExpected (OptDescs True)
           | UnRecognised
           | LError LexError

-- ### Process a token describing an option

data View : (o : OptDesc b) -> (tok : WithBounds Token) -> Type where
  IsOptReq : (a : String) -> View (REQ d) (MkBounded (CmdTok a) l q)
  IsOptOpt : (ma : String) -> (a : String) -> View (OPT ma d) (MkBounded (CmdTok a) l q)
  IsOptNot : View o tok

view : (o : OptDesc b) -> (tok : WithBounds Token) -> View o tok

view (REQ str) (MkBounded (CmdTok str1) l q) = IsOptReq str1
view (OPT str str1) (MkBounded (CmdTok str2) l q) = IsOptOpt str str2
view o t = IsOptNot

-- ### Process tokens
processArgs : (o : OptDescs b)
           -> List (WithBounds Token)
           -> Either Error (All BuildArg o)

processArgs [] [(MkBounded EndInput l q)]
  = Right Nil

processArgs [] xs
  = Left (ArgsEmpty (xs))

processArgs (x :: xs) []
  = Left (ToksExpected (x::xs))

processArgs [REST desc] xs = collect [<] xs where

  collect : SnocList String
           -> List (WithBounds Token)
           -> Either Error (Commands.All.All BuildArg [REST desc])
  collect acc [] = pure [unwords (acc <>> [])]
  collect acc [MkBounded EndInput _ _] = collect acc []
  collect acc (MkBounded Colon _ _ :: ys) = collect (acc :< ":") ys
  collect acc (MkBounded (CmdTok a) _ _ :: ys) = collect (acc :< a) ys
  collect acc (x :: xs) = Left (ToksExpected [REST desc])

processArgs (x :: xs) (y :: ys) with (view x y)
  processArgs ((REQ _) :: xs) ((MkBounded (CmdTok a) l q) :: ys) | (IsOptReq a)
    = do rest <- processArgs xs ys
         pure (a :: rest)

  -- Need to back track to see if an option has not been used...
  processArgs ((OPT ma _) :: xs) ((MkBounded (CmdTok a) l q) :: ys) | (IsOptOpt ma a)
    = case processArgs xs ((MkBounded (CmdTok a) l q)::ys) of
        Right rest => pure (ma :: rest)
        Left err => do rest <- processArgs xs ys
                       pure (a :: rest)

  processArgs (x :: xs) (y :: ys) | IsOptNot
    = Left ExpectedOption

-- ### Determine if a name was used.

data HasName : String -> (tok : WithBounds Token) -> Type where
  HN : (prf : a = b)
    -> HasName a (MkBounded (CmdTok b) l q)

Uninhabited (HasName a (MkBounded (NotRecognised b) l q)) where
  uninhabited (HN Refl) impossible

Uninhabited (HasName a (MkBounded (WS b) l q)) where
  uninhabited (HN Refl) impossible

Uninhabited (HasName a (MkBounded EndInput l q)) where
  uninhabited (HN Refl) impossible

Uninhabited (HasName a (MkBounded Colon l q))
  where uninhabited (HN Refl) impossible

hasName : (x   : String)
       -> (tok : WithBounds Token)
              -> Dec (HasName x tok)

hasName x (MkBounded (NotRecognised str) isIrrelevant bounds)
  = No absurd
hasName x (MkBounded (WS str) isIrrelevant bounds)
  = No absurd
hasName x (MkBounded EndInput isIrrelevant bounds)
  = No absurd
hasName x (MkBounded Colon isIrrelevant bounds)
  = No absurd

hasName x (MkBounded (CmdTok str) isIrrelevant bounds)
  = case decEq x str of
      Yes Refl => Yes (HN Refl)
      No  no  => No (\(HN Refl) => no Refl)

-- ### Cycle through the namespace

hasCorrectName : (ns : List String)
             -> (tok : WithBounds Token)
                    -> DecInfo Error
                               (Any (\x => HasName x tok) ns)
hasCorrectName [] tok
  = No NameExpected absurd
hasCorrectName (x :: xs) tok with (any (\x => hasName x tok) (x::xs))
  hasCorrectName (x :: xs) tok | (Yes prf)
    = Yes prf
  hasCorrectName (x :: xs) tok | (No contra)
    = No (WrongName (x::xs)) (\prf => contra prf)

-- ### Check the Colon

data IsColon : (tok : WithBounds Token) -> Type where
  ItIs : IsColon (MkBounded Colon l q)
  ItIsNot : IsColon (MkBounded tok l q)

isColon : (tok : WithBounds Token) -> IsColon tok
isColon (MkBounded (NotRecognised str) isIrrelevant bounds)
  = ItIsNot
isColon (MkBounded (WS str) isIrrelevant bounds)
  = ItIsNot
isColon (MkBounded (CmdTok str) isIrrelevant bounds)
  = ItIsNot
isColon (MkBounded EndInput isIrrelevant bounds)
  = ItIsNot
isColon (MkBounded Colon isIrrelevant bounds)
  = ItIs

data Result : OptDescs b -> List (WithBounds Token) -> Type where
  Empty : Result [] [MkBounded EndInput l q]

  Args  : {0 os : OptDescs True}
       -> All BuildArg os
       -> Result os toks

processArgsM : (a  : OptDescs b)
            -> (os : List (WithBounds Token))
                   -> Either Error (Result a os)
processArgsM [] [MkBounded EndInput l q]
  = pure Empty
processArgsM [] xs
  = Left (ArgsEmpty xs)

processArgsM (head :: tail) os with (processArgs (head :: tail) os)
  processArgsM (head :: tail) os | (Left x)
    = Left x
  processArgsM (head :: tail) os | (Right x)
    = Right (Args x)

buildArgs : All BuildArg os
         -> BuildArgs a os
         -> a
buildArgs [] f = f

buildArgs (x :: xs) f
  = buildArgs xs (f x)

processCmd : CommandDesc a
          -> List (WithBounds Token)
          -> Either Error a
processCmd (MkCDesc name argsDesc args help) Nil = Left IsVoid

processCmd (MkCDesc name argsDesc args help) (x :: (y :: xs))
  = case isColon x of
      ItIs
        => case hasCorrectName (forget name) y of
             (Yes prfWhy) => do res <- processArgsM argsDesc xs
                                case res of
                                  Empty => pure args
                                  Args z => pure (buildArgs z args)

             (No msg no)
               => Left msg

      ItIsNot => Left ColonExpected

processCmd (MkCDesc name argsDesc args help) (x::xs)
  = Left IsVoid

processCmds : List (CommandDesc a)
           -> List (WithBounds Token)
           -> Either Error a
processCmds [] ys
  = Left UnRecognised

processCmds (x :: xs) ys
  = case processCmd x ys of
      Left err => processCmds xs ys
      Right r => pure r


||| Given the command table, see if it is a valid command.
export
processCommand : Commands a
              -> String
              -> Either Error a
processCommand cs str
  = case lexString Commands.Lexer str of
      Left err => Left (LError err)
      Right toks
        => processCmds (forget cs) toks

-- [ EOF ]
