|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Velo.Parser

import Data.List1

import System.Path
import Velo.Core

import public Velo.Lexer
import Velo.Parser.API


import Velo.Types

import Velo.IR.AST

%default total

ref : Rule Raw
ref
  = map (\r => Branch (Ref (get r)) (span r) Nil)
        $ Velo.ref

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

null : Shape EXP 0 Nil -> FileContext -> Raw
null k fc = Branch k fc Nil

bool : Rule Raw
bool
   =  givesWithLoc "true"  (null T)
  <|> givesWithLoc "false" (null F)

mutual
  hole : Rule Raw
  hole
    = do s <- Toolkit.location
         symbol "?"
         commit
         h <- name
         e <- Toolkit.location
         pure (null (Hole h) (newFC s e))

  nat : Rule Raw
  nat = givesWithLoc "zero" (null Zero)
      <|> do s <- Toolkit.location
             symbol "("
             keyword "inc"
             commit
             i <- expr
             symbol ")"
             e <- Toolkit.location
             pure (Branch Plus (newFC s e) [i])

  add : Rule Raw
  add
    = do s <- Toolkit.location
         symbol "("
         keyword "add"
         commit
         l <- expr
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Branch Add (newFC s e) [l, r])

  and : Rule Raw
  and
    = do s <- Toolkit.location
         symbol "("
         keyword "and"
         commit
         l <- expr
         r <- expr
         symbol ")"
         e <- Toolkit.location
         pure (Branch And (newFC s e) [l, r])

  funAnon : Rule Raw
  funAnon =
    do s <- Toolkit.location
       symbol "("
       keyword "fun"
       commit
       n <- name
       symbol ":"
       ty <- type
       symbol "=>"
       body <- expr
       symbol ")"
       e <- Toolkit.location
       pure (Branch (Fun n ty) (newFC s e) [body])

  let_ : Rule Raw
  let_ = letNonRec
    where
      body : Location -> Bool -> Rule Raw
      body s isRec
        = do n <- name
             symbol "="
             v <- expr
             keyword "in"
             commit
             b <- expr
             e <- Toolkit.location
             pure (Branch (Let n) (newFC s e) [v, b])


      letNonRec : Rule Raw
      letNonRec
        = do s <- Toolkit.location
             keyword "let"
             body s False

  app : Rule Raw
  app =
    do s <- Toolkit.location
       symbol "("
       f <- expr
       a <- expr
       symbol ")"
       e <- Toolkit.location
       pure (Branch App (newFC s e) [f, a])

  ann : Rule Raw
  ann =
    do s <- Toolkit.location
       symbol "("
       a <- expr
       symbol ":"
       commit
       ty <- type
       symbol ")"
       e <- Toolkit.location
       pure (Branch (The ty) (newFC s e) [a])


  expr : Rule Raw
  expr =   ref
       <|> hole
       <|> nat <|> bool <|> and <|> add
       <|> let_
       <|> app
       <|> funAnon
       <|> ann

velo : Rule Raw
velo
  = expr


namespace Velo
  export
  fromString : (str : String)
                   -> Velo Raw
  fromString str
    = do ast <- parseString (\p => Parse (PError "REPL" p))
                Velo.Lexer
                velo
                str
         pure (map (setSource "REPL") ast)

  export
  fromFile : (fname : String)
                   -> Velo Raw
  fromFile fname
    = do ast <- parseFile (\p => Parse (PError fname p))
                Velo.Lexer
                velo
                fname
         pure $ (map (setSource fname) ast)



-- [ EOF ]
