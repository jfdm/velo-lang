||| Reasoning about elements in a DList based on their index.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DList.AtIndex

import Decidable.Equality

import Toolkit.Decidable.Informative

import Toolkit.Data.List.AtIndex
import Toolkit.Data.DList

%default total


||| Proof that some element satisfies the predicate
|||
||| @idx   The type of the element's index.
||| @type  The type of the list element.
||| @p     A predicate
||| @xs      The list itself.
public export
data HoldsAtIndex : (type   : Type)
                 -> (item   : type -> Type)
                 -> (p      : {i : type} -> (x : item i) -> Type)
                 -> {is     : List type}
                 -> (xs     : DList type item is)
                 -> (idx    : Nat)
                           -> Type
    where
      ||| Proof that the element is at the front of the list.
      Here : {p   : {i : type} -> (x : item i) -> Type}
          -> {i   : type}
          -> {x   : item i}
          -> (prf : p x)
                 -> HoldsAtIndex type item p (x::xs) Z


      ||| Proof that the element is found later in the list.
      There : {p      : {i : type} -> (x : item i) -> Type}
           -> (contra : p x' -> Void)
           -> (later  : HoldsAtIndex type item p      xs     loc)
                     -> HoldsAtIndex type item p (x'::xs) (S loc)

namespace Find
  namespace HoldsAtIndex
    public export
    data Error type = IsEmpty
                    | Later type (HoldsAtIndex.Error type)

  isEmpty : {p  : {i : type} -> (x : item i) -> Type}
         -> DPair Nat (HoldsAtIndex type item p [])
         -> Void
  isEmpty (MkDPair loc prf) with (prf)
    isEmpty (MkDPair loc prf) | (MkDPair _ (Here _)) impossible
    isEmpty (MkDPair loc prf) | (MkDPair _ (There _)) impossible


  notLater : {p : {i : type} -> (x : item i) -> Type}
          -> (DPair Nat (HoldsAtIndex type item p rest) -> Void)
          -> (p i -> Void)
          -> DPair Nat (HoldsAtIndex type item p (i :: rest))
          -> Void
  notLater f g (MkDPair _ (Here prf))
    = g prf
  notLater f g (MkDPair _ (There contra later))
    = f (MkDPair _ later)

  export
  holdsAtIndex : {p  : {i : type} -> (x : item i) -> Type}
              -> (f  : {i : type} -> (x : item i) -> DecInfo err (p x))
              -> (xs : DList type item is)
                    -> DecInfo (HoldsAtIndex.Error err)
                               (DPair Nat (HoldsAtIndex type item p xs))
  holdsAtIndex f Nil
    = No IsEmpty (isEmpty)

  holdsAtIndex f (x :: y) with (f x)
    holdsAtIndex f (x :: y) | (Yes prf)
      = Yes (MkDPair 0 (Here prf))

    holdsAtIndex f (x :: y) | (No msg contra) with (holdsAtIndex f y)
      holdsAtIndex f (x :: y) | (No msg contra) | (Yes (MkDPair loc prf))
        = Yes (MkDPair (S loc) (There contra prf))

      holdsAtIndex f (x :: y) | (No msg contra) | (No msgR contraR)
        = No (Later msg msgR)
             (notLater contraR contra)


-- [ EOF ]
