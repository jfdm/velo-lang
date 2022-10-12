||| Predicates for reasoning about elements of a SnocList, based on their
||| index.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.SnocList.AtIndex

import Decidable.Equality
import Toolkit.Decidable.Informative

%default total

public export
data AtIndex : (x   :      type)
            -> (xs  : SnocList type)
            -> (idx : Nat)
                   -> Type
  where
    Here : AtIndex x (xs :< x) Z
    There : (later : AtIndex x rest           idx)
                  -> AtIndex x (rest :< y) (S idx)

export
Uninhabited (AtIndex x [<] n) where
  uninhabited at impossible

export
irrelevantAtIndex : (p, q : AtIndex x xs n) -> p === q
irrelevantAtIndex Here Here = Refl
irrelevantAtIndex (There p) (There q) = cong There (irrelevantAtIndex p q)

namespace Check

  namespace IsAtIndex
    public export
    data Error = EmptySnocList
               | SupposedToBeHere
               | SupposedToBeLater
               | Later Error

  supposedToBeHere : (x = y -> Void) -> AtIndex x (xs :< y) 0 -> Void
  supposedToBeHere f Here = f Refl

  isNotLater : (AtIndex x xs k -> Void) -> AtIndex x (xs :< y) (S k) -> Void
  isNotLater f (There later) = f later

  export
  isAtIndex : DecEq type
           => (idx : Nat)
           -> (x   : type)
           -> (xs  : SnocList type)
                  -> DecInfo Error (AtIndex x xs idx)
  isAtIndex Z x [<]
    = No EmptySnocList absurd

  isAtIndex Z x (xs :< y) with (decEq x y)
    isAtIndex Z x (xs :< x) | (Yes Refl)
      = Yes Here
    isAtIndex Z x (xs :< y) | (No contra)
      = No SupposedToBeHere (supposedToBeHere contra)

  isAtIndex (S k) x [<]
    = No SupposedToBeLater absurd

  isAtIndex (S k) x (xs :< _) with (isAtIndex k x xs)
    isAtIndex (S k) x (xs :< _) | (Yes prf)
      = Yes (There prf)
    isAtIndex (S k) x (xs :< _) | (No msg contra)
      = No (Later msg) (isNotLater contra)

namespace Find

  namespace HasIndex
    public export
    data Error = IsEmpty
               | Later HasIndex.Error

  isEmpty : DPair Nat (AtIndex x [<]) -> Void
  isEmpty (MkDPair _ Here) impossible

  isNotElem : {x,y : type}
           -> (DPair Nat (AtIndex x xs) -> Void)
           -> (x = y -> Void)
           -> DPair Nat (AtIndex x (xs :< y))
           -> Void
  isNotElem {x} {y} f g (MkDPair fst snd) with (snd)
    isNotElem {x = x} {y = x} f g (MkDPair 0 snd) | Here
      = g Refl
    isNotElem {x = x} {y = y} f g (MkDPair (S idx) snd) | (There later)
      = f (MkDPair idx later)

  export
  hasIndex : DecEq type
          => (x : type)
          -> (xs : SnocList type)
                -> DecInfo HasIndex.Error
                           (DPair Nat (AtIndex x xs))
  hasIndex x [<]
    = No IsEmpty (isEmpty)
  hasIndex x (xs :< y) with (decEq x y)
    hasIndex x (xs :< x) | (Yes Refl)
      = Yes (MkDPair Z Here)

    hasIndex x (xs :< y) | (No contra) with (hasIndex x xs)
      hasIndex x (xs :< y) | (No contra) | (Yes (MkDPair idx prf))
        = Yes (MkDPair (S idx) (There prf))

      hasIndex x (xs :< y) | (No contra) | (No msg f)
        = No (Later msg) (isNotElem f contra)

-- [ EOF ]
