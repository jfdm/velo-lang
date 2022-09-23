|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Occurs.Does.Not

import Decidable.Equality

import Toolkit.Decidable.Informative

import Toolkit.Data.List.Occurs.Error


%default total

public export
data Occurs : (type : Type)
                 -> (p    : type -> Type)
                 -> (xs   : List type)
                 -> (cy   : Nat)
                         -> Type
  where
    End : Occurs type p Nil Z

    Yes : (holds : p x)
       -> (rest  : Occurs type p     xs  cn)
                -> Occurs type p (x::xs) cn

    No : (nope : Not (p x))
      -> (rest : Occurs type p     xs     cn)
              -> Occurs type p (x::xs) (S cn)

export
Uninhabited (Occurs type p Nil (S x)) where
  uninhabited End impossible
  uninhabited (Yes holds rest) impossible
  uninhabited (No nope rest) impossible

namespace Exactly

  shouldBeZero : (p x -> Void)
              -> Does.Not.Occurs type p (x :: xs) 0 -> Void
  shouldBeZero f (Yes holds rest) = f holds


  shouldNotOccurMore : (Does.Not.Occurs type p xs k -> Void)
                    -> (p x -> Void)
                    -> Does.Not.Occurs type p (x :: xs) (S k) -> Void
  shouldNotOccurMore f g (Yes holds rest) = g holds
  shouldNotOccurMore f g (No nope rest) = f rest

  wrongOccursNot : (Does.Not.Occurs type p xs cn -> Void)
                 -> p x
                 -> Does.Not.Occurs type p (x :: xs) cn -> Void
  wrongOccursNot f y (Yes holds rest) = f rest
  wrongOccursNot f y (No nope rest) = nope y

  export
  doesNotExactlyOccur : {type : Type}
              -> {p    : type -> Type}
              -> (f    : (this : type) -> Dec (p this))
              -> (xs   : List type)
              -> (cn   : Nat)
                      -> DecInfo Occurs.Error
                                 (Does.Not.Occurs type p xs cn)
  doesNotExactlyOccur f [] Z
    = Yes End

  doesNotExactlyOccur f [] (S k)
    = No (MkError Z (S k))
         absurd

  doesNotExactlyOccur f (x :: xs) cn with (f x)
    doesNotExactlyOccur f (x :: xs) cn | (Yes prf) with (doesNotExactlyOccur f xs cn)
      doesNotExactlyOccur f (x :: xs) cn | (Yes prf) | (Yes y)
        = Yes (Yes prf y)

      doesNotExactlyOccur f (x :: xs) cn | (Yes prf) | (No msg contra)
        = No (MkError cn (found msg))
             (wrongOccursNot contra prf)

    doesNotExactlyOccur f (x :: xs) cn | (No contra) with (cn)

      doesNotExactlyOccur f (x :: xs) cn | (No contra) | 0
        = No (MkError cn Z)
             (shouldBeZero contra)

      doesNotExactlyOccur f (x :: xs) cn | (No contra) | (S k) with (doesNotExactlyOccur f xs k)
        doesNotExactlyOccur f (x :: xs) cn | (No contra) | (S k) | (Yes prf)
          = Yes (No contra prf)

        doesNotExactlyOccur f (x :: xs) cn | (No contra) | (S k) | (No msg g)
          = No (MkError cn (S k))
               (shouldNotOccurMore g contra)


-- [ EOF ]
