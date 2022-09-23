||| Predicates for reasoning about elements of a list, based on their
||| index.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.AtIndex

import Decidable.Equality
import Toolkit.Decidable.Informative

%default total

public export
data AtIndex : (x   :      type)
            -> (xs  : List type)
            -> (idx : Nat)
                   -> Type
  where
    Here : AtIndex x (x::xs) Z
    There : (later : AtIndex x     rest     idx)
                  -> AtIndex x (y::rest) (S idx)

namespace Check

  namespace IsAtIndex
    public export
    data Error = EmptyList
               | SupposedToBeHere
               | SupposedToBeLater
               | Later Error

  listIsEmpty : AtIndex x [] 0 -> Void
  listIsEmpty Here impossible
  listIsEmpty (There later) impossible

  supposedToBeHere : (x = y -> Void) -> AtIndex x (y :: xs) 0 -> Void
  supposedToBeHere f Here = f Refl

  supposedToBeLater : AtIndex x [] (S k) -> Void
  supposedToBeLater Here impossible
  supposedToBeLater (There later) impossible

  isNotLater : (AtIndex x xs k -> Void) -> AtIndex x (y :: xs) (S k) -> Void
  isNotLater f (There later) = f later

  export
  isAtIndex : DecEq type
           => (idx : Nat)
           -> (x   : type)
           -> (xs  : List type)
                  -> DecInfo Error (AtIndex x xs idx)
  isAtIndex Z x []
    = No EmptyList (listIsEmpty)

  isAtIndex Z x (y :: xs) with (decEq x y)
    isAtIndex Z x (x :: xs) | (Yes Refl)
      = Yes Here
    isAtIndex Z x (y :: xs) | (No contra)
      = No SupposedToBeHere (supposedToBeHere contra)

  isAtIndex (S k) x []
    = No SupposedToBeLater (supposedToBeLater)

  isAtIndex (S k) x (_ :: xs) with (isAtIndex k x xs)
    isAtIndex (S k) x (_ :: xs) | (Yes prf)
      = Yes (There prf)
    isAtIndex (S k) x (_ :: xs) | (No msg contra)
      = No (Later msg) (isNotLater contra)

namespace Find

  namespace HasIndex
    public export
    data Error = IsEmpty
               | Later HasIndex.Error

  isEmpty : DPair Nat (AtIndex x []) -> Void
  isEmpty (MkDPair _ Here) impossible

  isNotElem : {x,y : type}
           -> (DPair Nat (AtIndex x xs) -> Void)
           -> (x = y -> Void)
           -> DPair Nat (AtIndex x (y :: xs))
           -> Void
  isNotElem {x} {y} f g (MkDPair fst snd) with (snd)
    isNotElem {x = x} {y = x} f g (MkDPair 0 snd) | Here
      = g Refl
    isNotElem {x = x} {y = y} f g (MkDPair (S idx) snd) | (There later)
      = f (MkDPair idx later)

  export
  hasIndex : DecEq type
          => (x : type)
          -> (xs : List type)
                -> DecInfo HasIndex.Error
                           (DPair Nat (AtIndex x xs))
  hasIndex x []
    = No IsEmpty (isEmpty)
  hasIndex x (y :: xs) with (decEq x y)
    hasIndex x (x :: xs) | (Yes Refl)
      = Yes (MkDPair Z Here)

    hasIndex x (y :: xs) | (No contra) with (hasIndex x xs)
      hasIndex x (y :: xs) | (No contra) | (Yes (MkDPair idx prf))
        = Yes (MkDPair (S idx) (There prf))

      hasIndex x (y :: xs) | (No contra) | (No msg f)
        = No (Later msg) (isNotElem f contra)

-- [ EOF ]
