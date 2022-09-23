|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Interleaving

%default total

infixr 6 <::
infixr 6 ::>

public export
data Interleaving : (xs, ys, zs : List type) -> Type where
  Empty   : Interleaving Nil Nil Nil

  Left : {xs,ys,zs : List type}
      -> (x : type)
      -> (rest : Interleaving xs ys zs)
              -> Interleaving (x::xs) ys (x::zs)
  Right : {xs,ys,zs : List type}
       -> (y : type)
       -> (rest : Interleaving xs ys zs)
               -> Interleaving xs (y::ys) (y::zs)

public export
(<::) : {xs,ys,zs : List type}
     -> (x : type)
     -> (rest : Interleaving xs ys zs)
             -> Interleaving (x::xs) ys (x::zs)
(<::) = Left

public export
(::>) : {xs,ys,zs : List type}
     -> (y : type)
     -> (rest : Interleaving xs ys zs)
             -> Interleaving xs (y::ys) (y::zs)
(::>) = Right
