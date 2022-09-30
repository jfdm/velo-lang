module Velo.IR.AST

import Data.String

import Data.List1

import public Toolkit.Data.Location

import Velo.Types

%default total


namespace Velo
  public export
  data AST a = Ref a String

             | Hole a String
             | Zero a
             | Plus a (AST a)

             | Add a (AST a) (AST a)

             | T a
             | F a

             | And a (AST a) (AST a)

             | Let a String (AST a) (AST a)

             | Fun a String Ty (AST a)
             | App a (AST a) (AST a)

             | The a Ty (AST a)

  public export
  Raw : Type
  Raw = AST FileContext


map : (a -> b) -> AST a -> AST b
map f (Ref x str)
  = Ref (f x) str

map f (Hole x str)
  = Hole (f x) str

map f (Zero x)
  = Zero (f x)

map f (Plus x y)
  = Plus (f x) (map f y)

map f (Add x y z)
  = Add (f x) (map f y) (map f z)

map f (T x)
  = T (f x)

map f (F x)
  = F (f x)

map f (And x y z)
  = And (f x) (map f y) (map f z)

map f (Let x str w z)
  = Let (f x) str (map f w) (map f z)

map f (Fun x str y z)
  = Fun (f x)
        str
        y
        (map f z)

map f (App x y z)
  = App (f x) (map f y) (map f z)

map f (The x y z)
  = The (f x) y (map f z)


export
Functor AST where
  map f a = map f a

export
getFC : AST FileContext -> FileContext
getFC (Ref x str)       = x
getFC (Hole x str)      = x
getFC (Zero x)          = x
getFC (Plus x y)        = x
getFC (Add x y z)       = x
getFC (T x)             = x
getFC (F x)             = x
getFC (And x y z)       = x
getFC (Let x str z w)   = x
getFC (Fun x str y z)   = x
getFC (App x y z)       = x
getFC (The x y z)       = x


-- [ EOF ]
