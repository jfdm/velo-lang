|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Velo.Parser

import Data.List1

import Velo.Core

import public Velo.Lexer
import Velo.Parser.API


import Velo.Types

import Velo.AST

%default total

ref : Rule (AST FileContext)
ref
  = do r <- Velo.ref
       pure (Ref (span r) (get r))

mutual

  typeFunc : Rule Ty
  typeFunc
    = do symbol "("
         a <- type
         symbol "->"
         bs <- type
         symbol ")"
         pure $ TyFunc a bs


  type : Rule Ty
  type =  gives "nat"  TyNat
      <|> gives "bool" TyBool
      <|> typeFunc

bool : Rule (AST FileContext)
bool =  givesWithLoc "true"  (T)
    <|> givesWithLoc "false" (F)

mutual
  hole : Rule (AST FileContext)
  hole
    = do s <- Toolkit.location
         symbol "?"
         h <- name
         e <- Toolkit.location
         pure (Hole (newFC s e) h)

  nat : Rule (AST FileContext)
  nat = givesWithLoc "zero" Zero
      <|> do s <- Toolkit.location
             symbol "("
             keyword "inc"
             i <- expr
             symbol ")"
             e <- Toolkit.location
             pure (Plus (newFC s e) i)

  add : Rule (AST FileContext)
  add
    = do s <- Toolkit.location
         symbol "("
         keyword "add"
         l <- expr
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Add (newFC s e) l r)

  and : Rule (AST FileContext)
  and
    = do s <- Toolkit.location
         symbol "("
         keyword "and"
         l <- expr
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (And (newFC s e) l r)

  funAnon : Rule (AST FileContext)
  funAnon =
    do s <- Toolkit.location
       symbol "("
       keyword "fun"
       n <- name
       symbol ":"
       ty <- type
       symbol "=>"
       body <- expr
       symbol ")"
       e <- Toolkit.location
       pure (Fun (newFC s e) n ty body)

  let_ : Rule (AST FileContext)
  let_ = letNonRec
    where
      body : Location -> Bool -> Rule (AST FileContext)
      body s isRec
        = do n <- name
             symbol "="
             v <- expr
             keyword "in"
             b <- expr
             e <- Toolkit.location
             pure (Let (newFC s e) n v b)


      letNonRec : Rule (AST FileContext)
      letNonRec
        = do s <- Toolkit.location
             keyword "let"
             body s False

  app : Rule (AST FileContext)
  app =
    do s <- Toolkit.location
       symbol "("
       f <- expr
       a <- expr
       symbol ")"
       e <- Toolkit.location
       pure (App (newFC s e) f a)

  expr : Rule (AST FileContext)
  expr =   ref
       <|> hole
       <|> nat <|> bool <|> and <|> add
       <|> let_
       <|> app
       <|> funAnon

velo : Rule (AST FileContext)
velo
  = expr


namespace Velo
  export
  fromString : (str : String)
                   -> Velo (AST FileContext)
  fromString str
    = do ast <- parseString (\p => Parse (PError "REPL" p))
                Velo.Lexer
                velo
                str
         pure (map (setSource "REPL") ast)

  export
  fromFile : (fname : String)
                   -> Velo (AST FileContext)
  fromFile fname
    = do ast <- parseFile (\p => Parse (PError fname p))
                Velo.Lexer
                velo
                fname
         pure (map (setSource fname) ast)


-- [ EOF ]
