module Toolkit.AST

import public Data.Vect
import public Toolkit.Data.Location
import public Toolkit.Data.DVect

public export
data AST : (desc       : (k     : kind)
                      -> (arity : Nat)
                      -> (meta  : Vect arity kind)
                               -> Type)
        -> (k          : kind)
        -> (annotation : Type)
                      -> Type
  where

  Branch : {0 node  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
        -> (  desc  : node k n meta)
        -> (  annot : a)
        -> (  nodes : DVect kind (\k => AST node k a) n meta)
                   -> AST node k a

export
getAnnotation : AST d k a -> a
getAnnotation (Branch kind annot nodes)
  = annot

export
Functor (AST kinds k) where
  map f (Branch kind annot nodes)
    = Branch kind (f annot) (mapV f nodes)

    where mapV : (f : a -> b) -> DVect d (\k => AST node k a) n ks
                              -> DVect d (\k => AST node k b) n ks
          mapV f [] = []
          mapV f (x :: xs) = map f x :: mapV f xs



namespace Generic
  export
  show : {0 node  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
      -> (showDesc : forall k, arity, ms . (desc : node k arity ms)
                          -> String)
      -> (showAnn  : (annot : a) -> String)
      -> (ast      : AST node k a)
                  -> String


  show k a (Branch kind annot nodes)
    = "(Branch \{k kind} \{a annot} \{showDVect (show k a) nodes})"

namespace Default
  export
   {0 node  : (k : kind) -> (n : Nat) -> Vect n kind -> Type}
   -> (forall k,n,ms . Show (node k n ms))
      => Show a
      => Show (AST node k a) where

        show = assert_total $ show show show


public export
data AsRef : String -> FileContext -> Ref -> Type where
  R : AsRef s fc (MkRef fc s)

export
asRef : (s : String) -> (fc : FileContext) -> AsRef s fc (MkRef fc s)
asRef s fc = R

namespace Singleton
  public export
  data Singleton : (Nat -> Type) -> Unit -> (n : Nat) -> Vect n Unit -> Type where
    Val : s n -> Singleton s () n (replicate n ())

-- [ EOF ]
