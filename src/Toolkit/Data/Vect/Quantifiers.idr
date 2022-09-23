||| Error returning quantifiers for Vectors
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Vect.Quantifiers

import public Toolkit.Decidable.Informative
import        Data.Vect

import        Data.Vect.Quantifiers
import        Data.Vect.AtIndex

%default total

namespace Informative

  namespace All
    namespace NotAll
      public export
      data NotAll : (p  : (x : type) -> Type)
                 -> (e  : (x : type) -> Type)
                 -> (xs : Vect n type)
                       -> Type
        where
          Here : {0 e : (a : type) -> Type}
              -> {  x : type}
              -> (msg : e x)
              -> (prf : p x -> Void)
                     -> NotAll p e (x::xs)

          There : {0 p     : (a : type) -> Type}
               -> (  prf   :        p    x)
               -> (  later : NotAll p e     xs)
                          -> NotAll p e (x::xs)

    export
    position : NotAll p e xs -> Nat
    position (Here _ _)
      = Z
    position (There _ later)
      = S (position later)

    export
    error : NotAll p e xs -> (x ** e x)
    error (Here m _)
      = (_ ** m)
    error (There _ later)
      = error later

    export
    errorAt : NotAll p e xs -> (Nat, (x ** e x))
    errorAt (Here msg _)
      = (Z, (_ ** msg))

    errorAt (There _ later) with (errorAt later)
      errorAt (There _ later) | (loc, m) = (S loc, m)

  export
  all : (f  : (x : a)
                -> DecInfo (e x) (p x))
     -> (xs : Vect n a)
           -> DecInfo (NotAll p e xs)
                      (All    p   xs)
  all f []
    = Yes []

  all f (x :: xs) with (f x)
    all f (x :: xs) | (Yes pH) with (all f xs)
      all f (x :: xs) | (Yes pH) | (Yes pT)
        = Yes (pH :: pT)

      all f (x :: xs) | (Yes pH) | (No m c)
        = No (There pH m)
             (\(y::ys) => c ys)

    all f (x :: xs) | (No m c)
      = No (Here m c)
           (\(y::ys) => c y)

-- [ EOF ]
