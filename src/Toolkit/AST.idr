module Toolkit.AST

import public Data.Vect

import public Toolkit.Data.Location

public export
data AST : (desc : Nat -> Type) -> (a : Type) -> Type where

  Branch : {0 node  : Nat -> Type}
        -> (  kind  : node n)
        -> (  annot : a)
        ->  (nodes  : Vect n (AST node a))
                   -> AST node a

export
getAnnotation : AST k a -> a
getAnnotation (Branch kind annot nodes)
  = annot

export
Functor (AST kinds) where
  map f (Branch kind annot nodes)
    = Branch kind (f annot) (mapV f nodes)

    where mapV : (f : a -> b) -> Vect n (AST node a)
                              -> Vect n (AST node b)
          mapV f [] = []
          mapV f (x :: xs) = map f x :: mapV f xs



mutual
  showV : (forall n . (kinds n) -> String)
       -> (a -> String)
       -> Vect x (AST kinds a)
       -> Vect x String
  showV k a Nil
    = Nil
  showV k a (x::xs)
    = show k a x :: showV k a xs

  namespace Generic
    export
    show : (forall n . (kinds n) -> String)
        -> (a -> String)
        -> AST kinds a
        -> String
    show k a (Branch kind annot nodes)
      = let ns = showV k a nodes
        in "(Branch \{k kind} \{a annot} \{show ns})"

  namespace Default
    export
    (forall n . Show (kinds n))
        => Show a
        => Show (AST kinds a) where

          show = show show show

public export
data AsRef : String -> FileContext -> Ref -> Type where
  R : AsRef s fc (MkRef fc s)

export
asRef : (s : String) -> (fc : FileContext) -> AsRef s fc (MkRef fc s)
asRef s fc = R

-- [ EOF ]
