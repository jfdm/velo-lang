|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Occurs.Does

import Decidable.Equality

import Data.Nat

import Toolkit.Decidable.Informative

import public Toolkit.Data.List.Occurs.Error


%default total

namespace Exactly
  public export
  data Occurs : (type : Type)
             -> (p    : type -> Type)
             -> (xs   : List type)
             -> (cy   : Nat)
                     -> Type
    where
      End : Occurs type p Nil Z

      Yes : (holds : p x)
         -> (rest  : Occurs type p     xs     cy)
                  -> Occurs type p (x::xs) (S cy)

      No : (nope : Not (p x))
        -> (rest : Occurs type p     xs  cy)
                -> Occurs type p (x::xs) cy

  export
  Uninhabited (Occurs type p Nil (S x)) where
    uninhabited End impossible
    uninhabited (Yes holds rest) impossible
    uninhabited (No nope rest) impossible

  namespace Check
    shouldHaveOneMore : (p x)
                     -> (Occurs type p       xs     k  -> Void)
                     ->  Occurs type p (x :: xs) (S k) -> Void
    shouldHaveOneMore prf f (Yes holds rest) = f rest
    shouldHaveOneMore prf f (No nope rest) = nope prf

    wrongOccurs : (Occurs type p       xs  cy -> Void)
               -> (p x -> Void)
               ->  Occurs type p (x :: xs) cy -> Void
    wrongOccurs f g (Yes holds rest) = g holds
    wrongOccurs f g (No nope rest) = f rest

    namespace Exactly
      export
      occurs : {type : Type}
            -> {p    : type -> Type}
            -> (f    : (this : type) -> Dec (p this))
            -> (xs   : List type)
            -> (cy   : Nat)
                    -> DecInfo Occurs.Error
                               (Occurs type p xs cy)
      occurs f [] Z
        = Yes End

      occurs f [] (S k)
        = No (MkError (S k) Z) absurd

      occurs f (x :: xs) cy with (f x)
        occurs f (x :: xs) cy | (Yes prf) with (cy)
          occurs f (x :: xs) cy | (Yes prf) | Z
            = No (MkError Z 1)
                 (\(No f x) => f prf)

          occurs f (x :: xs) cy | (Yes prf) | (S k) with (occurs f xs k)
            occurs f (x :: xs) cy | (Yes prf) | (S k) | (Yes y)
              = Yes (Yes prf y)

            occurs f (x :: xs) cy | (Yes prf) | (S k) | (No msg contra)
              = No (MkError (S k) (S $ found msg))
                   (shouldHaveOneMore prf contra)

        occurs f (x :: xs) cy | (No contra) with (occurs f xs cy)
          occurs f (x :: xs) cy | (No contra) | (Yes prf)
            = Yes (No contra prf)

          occurs f (x :: xs) cy | (No contra) | (No msg g)
            = No (MkError cy (found msg))
                 (wrongOccurs g contra)

  namespace Discover

    namespace Exactly
      export
      occurs : {type : Type}
            -> {p    : type -> Type}
            -> (f    : (this : type) -> Dec (p this))
            -> (xs   : List type)
                    -> DPair Nat (Occurs type p xs)
      occurs f []
        = MkDPair 0 End
      occurs f (x :: xs) with (f x)
        occurs f (x :: xs) | (Yes prf) with (Discover.Exactly.occurs f xs)
          occurs f (x :: xs) | (Yes prf) | (MkDPair fst snd)
            = MkDPair (S fst) (Yes prf snd)
        occurs f (x :: xs) | (No contra) with (Discover.Exactly.occurs f xs)
          occurs f (x :: xs) | (No contra) | (MkDPair fst snd)
            = MkDPair fst (No contra snd)

namespace AtLeast

  public export
  data Occurs : (type : Type)
             -> (p    : type -> Type)
             -> (xs   : List type)
             -> (ym   : Nat)
                     -> Type
    where
      EndY : (holds : p x) -> AtLeast.Occurs type p (x::xs) (S Z)

      Yes : (holds : p x)
         -> (rest  : AtLeast.Occurs type p     xs     cy)
                  -> AtLeast.Occurs type p (x::xs) (S cy)

      No : (nope : Not (p x))
        -> (rest : AtLeast.Occurs type p     xs  (S cy))
                -> AtLeast.Occurs type p (x::xs) (S cy)

  export
  Uninhabited (AtLeast.Occurs type p Nil (S x)) where
    uninhabited (EndY holds) impossible
    uninhabited (Yes holds rest) impossible
    uninhabited (No nope rest) impossible

  export
  Uninhabited (AtLeast.Occurs type p xs Z) where
    uninhabited (EndY holds) impossible
    uninhabited (Yes holds rest) impossible
    uninhabited (No nope rest) impossible

  namespace Check

    namespace AtLeast


      shouldBeAtLeastOne : (AtLeast.Occurs type p       xs 1 -> Void)
                        -> (p x -> Void)
                        ->  AtLeast.Occurs type p (x :: xs) 1 -> Void
      shouldBeAtLeastOne f g (EndY holds) = g holds
      shouldBeAtLeastOne f g (Yes holds rest) = g holds
      shouldBeAtLeastOne f g (No nope rest) = f rest

      shouldBeAtLeastOneMore : (AtLeast.Occurs type p    xs        (S k)  -> Void)
                            -> p x
                            ->  AtLeast.Occurs type p (x :: xs) (S (S k)) -> Void
      shouldBeAtLeastOneMore f y (Yes holds rest) = f rest
      shouldBeAtLeastOneMore f y (No nope rest) = nope y

      shouldBeAtLeastN : (AtLeast.Occurs type p       xs  (S (S k)) -> Void)
                      -> (p x -> Void)
                      ->  AtLeast.Occurs type p (x :: xs) (S (S k)) -> Void
      shouldBeAtLeastN f g (Yes holds rest) = g holds
      shouldBeAtLeastN f g (No nope rest) = f rest

      export
      occurs : {type : Type}
            -> {p    : type -> Type}
            -> (f    : (this : type) -> Dec (p this))
            -> (xs   : List type)
            -> (cy   : Nat)
                    -> DecInfo (Maybe Occurs.Error)
                               (AtLeast.Occurs type p xs cy)
      occurs f xs 0
        = No Nothing absurd

      occurs f [] (S k)
        = No (Just (MkError (S k) Z))
             absurd

      occurs f (x :: xs) (S 0) with (f x)
        occurs f (x :: xs) (S 0) | (Yes prf)
          = Yes (EndY prf)

        occurs f (x :: xs) (S 0) | (No contra) with (AtLeast.occurs f xs (S 0))
          occurs f (x :: xs) (S 0) | (No contra) | (Yes prfWhy)
            = Yes (No contra prfWhy)

          occurs f (x :: xs) (S 0) | (No contra) | (No msgWhyNot prfWhyNot)
            = No (map ({ expected := 1}) msgWhyNot)
                 (shouldBeAtLeastOne prfWhyNot contra)

      occurs f (x :: xs) (S (S k)) with (f x)
        occurs f (x :: xs) (S (S k)) | (Yes prf) with (AtLeast.occurs f xs (S k))
          occurs f (x :: xs) (S (S k)) | (Yes prf) | (Yes prfWhy)
            = Yes (Yes prf prfWhy)

          occurs f (x :: xs) (S (S k)) | (Yes prf) | (No msgWhyNot prfWhyNot)
            = No (map ({ expected := S (S k), found $= S}) msgWhyNot)
                 (shouldBeAtLeastOneMore prfWhyNot prf)

        occurs f (x :: xs) (S (S k)) | (No contra) with (AtLeast.occurs f xs (S (S k)))
          occurs f (x :: xs) (S (S k)) | (No contra) | (Yes prfWhy)
            = Yes (No contra prfWhy)

          occurs f (x :: xs) (S (S k)) | (No contra) | (No msgWhyNot prfWhyNot)
            = No (map ({ expected := S (S k)}) msgWhyNot)
                 (shouldBeAtLeastN prfWhyNot contra)

-- [ EOF ]
