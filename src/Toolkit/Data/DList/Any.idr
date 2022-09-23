||| The Any list quantifier for the DList quantifier.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DList.Any

import Toolkit.Decidable.Informative

import Toolkit.Data.DList

import public Toolkit.Decidable.Equality.Indexed

%default total

||| Proof that some element satisfies the predicate
|||
||| @idx   The type of the element's index.
||| @type  The type of the list element.
||| @p     A predicate
||| @xs      The list itself.
public export
data Any : (idx    : Type)
        -> (type   : idx -> Type)
        -> (p      : {i : idx} -> (x : type i) -> Type)
        -> {is     : List idx}
        -> (xs     : DList idx type is)
                  -> Type
    where
      ||| Proof that the element is at the front of the list.
      H : {p : {i : idx} -> (x : type i) -> Type}
       -> {i   : idx}
       -> {y   : type i}
       -> (prf : p y)
              -> Any idx type p (y :: xs)

      ||| Proof that the element is found later in the list.
      T : {p : {i : idx} -> (x : type i) -> Type}
       -> (contra : p x' -> Void)
       -> (later : Any idx type p       xs)
                -> Any idx type p (x' ::xs)

empty : {p : {i : idx} -> (x : type i) -> Type} -> Any idx type p Nil -> Void
empty (H prf) impossible
empty (T contra later) impossible


isNotThere : {p : {i : idx} -> (x : type i) -> Type}
          -> (Any idx type p rest -> Void)
          -> (p i -> Void)
          -> Any idx type p (i :: rest) -> Void
isNotThere f g (H prf) = g prf
isNotThere f g (T contra later) = f later

export
any : {p : {i : idx} -> (x : type i) -> Type}
   -> (f : {i : idx} -> (x : type i) -> DecInfo err (p x))
   -> (xs : DList idx type is)
         -> Dec (Any idx type p xs)
any f [] = No empty

any f (elem :: rest) with (f elem)
  any f (elem :: rest) | (Yes prfWhy)
    = Yes (H prfWhy)

  any f (elem :: rest) | (No msgWhyNot prfWhyNot) with (any f rest)
    any f (elem :: rest) | (No msgWhyNot prfWhyNot) | (Yes prfWhy)
      = Yes (T prfWhyNot prfWhy)
    any f (elem :: rest) | (No msgWhyNot prfWhyNot) | (No g)
      = No (isNotThere g prfWhyNot)

-- [ EOF ]
