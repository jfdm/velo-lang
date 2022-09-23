||| The Elem list quantifier for the DList quantifier.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DList.Elem

import Toolkit.Data.DList

import public Toolkit.Decidable.Equality.Indexed

%default total

||| Proof that some element is found in a `DList`.
|||
||| @iTy     The type of the element's index.
||| @elemTy  The type of the list element.
||| @x       An element in the list.
||| @xs      The list itself.
||| @prf     Proof that the element's index is in the list in the same position as the element itself.
public export
data Elem : (iTy    : Type)
         -> (elemTy : iTy -> Type)
         -> forall i, is
          . (x      : elemTy i)
         -> (xs     : DList iTy elemTy is)
         -> Type
    where
      ||| Proof that the element is at the front of the list.
      H : (Equals ity elemTy x y) -> Elem ity elemTy x (y :: xs)

      ||| Proof that the element is found later in the list.
      T : (later : Elem iTy elemTy x       xs)
                -> Elem iTy elemTy x (x' ::xs)


listEmpty : Elem type e thing Nil -> Void
listEmpty (H x) impossible
listEmpty (T later) impossible

notInLater : (contraE : Equals type e x y -> Void)
          -> (contraR : Elem type e x xs -> Void)
          -> (prf    : Elem type e x (y::xs))
                    -> Void
notInLater contraE contraR (H z) = contraE z
notInLater contraE contraR (T later) = contraR later


export
isElem : {type : Type}
      -> {e    : type -> Type}
      -> DecEq type
      => DecEqIdx type e
      => {a      : type}
      -> {as     : List type}
      -> (thing  : e a)
      -> (things : DList type e as)
                -> Dec (Elem type e thing things)
isElem thing [] = No listEmpty
isElem thing (elem :: rest) with (Index.decEq thing elem)
  isElem thing (thing :: rest) | (Yes (Same Refl Refl)) = Yes (H (Same Refl Refl))
  isElem thing (elem :: rest) | (No contra) with (isElem thing rest)
    isElem thing (elem :: rest) | (No contra) | (Yes prf) = Yes (T prf)
    isElem thing (elem :: rest) | (No contra) | (No f) = No (notInLater contra f)
-- [ EOF ]
