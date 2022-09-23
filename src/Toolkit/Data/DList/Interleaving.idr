||| Everything has a place.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DList.Interleaving

import public Toolkit.Data.List.Interleaving

import Toolkit.Data.DList

%default total

public export
data Interleaving : (a : Type)
                 -> (type : a -> Type)
                 -> {ls, rs, os : List a}
                 -> (lefts  : DList a type ls)
                 -> (rights : DList a type rs)
                 -> (orig   : DList a type os)
                 -> (prf    : Interleaving ls rs os)
                           -> Type
  where
    Empty : Interleaving a type Nil Nil Nil Empty

    Left  : {a : Type}
         -> {type : a -> Type}
         -> {x : a}
         -> {xs, ys, zs : List a}
         -> {ls   : DList a type xs}
         -> {rs   : DList a type ys}
         -> {os   : DList a type zs}
         -> {prf  : Interleaving xs ys zs}
         -> (head : type x)
         -> (tail : Interleaving a type        ls  rs        os         prf)
                 -> Interleaving a type (head::ls) rs (head::os) (x <:: prf)

    Right : {a : Type}
         -> {type : a -> Type}
         -> {y : a}
         -> {xs, ys, zs : List a}
         -> {ls   : DList a type xs}
         -> {rs   : DList a type ys}
         -> {os   : DList a type zs}
         -> {prf  : Interleaving xs ys zs}
         -> (head : type y)
         -> (tail : Interleaving a type ls        rs         os         prf)
                 -> Interleaving a type ls (head::rs) (head::os) (y ::> prf)

(<::) : {a : Type}
     -> {type : a -> Type}
     -> {x    : a}
     -> {xs, ys, zs : List a}
     -> {ls   : DList a type xs}
     -> {rs   : DList a type ys}
     -> {os   : DList a type zs}
     -> {prf  : Interleaving xs ys zs}
     -> (head : type x)
     -> (tail : Interleaving a type        ls  rs        os         prf)
             -> Interleaving a type (head::ls) rs (head::os) (x <:: prf)
(<::) = Left

(::>) : {a : Type}
     -> {type : a -> Type}
     -> {xs, ys, zs : List a}
     -> {ls   : DList a type xs}
     -> {rs   : DList a type ys}
     -> {os   : DList a type zs}
     -> {prf  : Interleaving xs ys zs}
     -> {y    : a}
     -> (head : type y)
     -> (tail : Interleaving a type ls        rs         os         prf)
             -> Interleaving a type ls (head::rs) (head::os) (y ::> prf)
(::>) = Right
