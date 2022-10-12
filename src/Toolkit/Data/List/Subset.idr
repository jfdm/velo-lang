|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Subset

import Data.List
import Toolkit.Data.List.Quantifiers
import Toolkit.Decidable.Informative

%default total

public export
data Subset : (eq   : a -> b -> Type)
           -> (this : List a)
           -> (that : List b)
                   -> Type
  where
    Empty : Subset eq Nil Nil

    Keep : {0 eq : a -> b -> Type}
        -> (prf  :        eq  x       y)
        -> (rest : Subset eq    xs      ys)
                -> Subset eq (x::xs) (y::ys)

    Skip : (rest : Subset eq xs     ys)
                -> Subset eq xs (y::ys)

namespace All

  export
  action : (compat : forall x, y. p y -> eq x y -> q x) ->
           All p ys -> Subset eq xs ys -> All q xs
  action compat pxs Empty = []
  action compat (px :: pxs) (Keep prf rest) = compat px prf :: action compat pxs rest
  action compat (px :: pxs) (Skip rest) = action compat pxs rest

namespace SnocList
  export
  Skips : {zs : SnocList b} -> Subset eq xs ys -> Subset eq xs (zs <>> ys)
  Skips {zs = [<]} rest
    = rest
  Skips {zs = (sx :< x)} rest = Skips (Skip rest)

export
Skips : {zs : List b} -> Subset eq xs ys -> Subset eq xs (zs ++ ys)
Skips {zs = []} rest = rest
Skips {zs = z :: zs} rest = Skip (Subset.Skips rest)

export
EmptyThis : {xs : List b} -> Subset eq [] xs
EmptyThis {xs = []} = Empty
EmptyThis {xs = x :: xs} = Skip EmptyThis

export
trans : (forall x, y, z. eq x y -> eq y z -> eq x z) ->
        (Subset eq xs ys -> Subset eq ys zs -> Subset eq xs zs)
trans tr th Empty = th
trans tr (Keep prf1 th) (Keep prf2 ph) = Keep (tr prf1 prf2) (trans tr th ph)
trans tr (Skip th) (Keep prf ph) = Skip (trans tr th ph)
trans tr th (Skip ph) = Skip (trans tr th ph)

export
(++) : Subset eq xs ys -> Subset eq as bs ->
       Subset eq (xs ++ as) (ys ++ bs)
Empty ++ ph = ph
Keep prf th ++ ph = Keep prf (th ++ ph)
Skip th ++ ph = Skip (th ++ ph)

public export
data Error : Type -> Type where
  EmptyThat : Error a
  Fail : a -> Error a
  FailThere : Error a -> Error a

emptyThat : Subset eq (x :: xs) [] -> Void
emptyThat Empty impossible

yesButNo : {eq : a -> b -> Type}
        -> {x : a} -> {xs : List a}
        -> {y : b} -> {ys : List b}
        -> (h : Subset eq     xs       ys -> Void)
        -> (t : Subset eq (x::xs)      ys -> Void)
             -> Subset eq (x::xs) (y::ys)
             -> Void
yesButNo h t (Keep prf rest) = h rest
yesButNo h t (Skip rest) = t rest

justNot : {eq : a -> b -> Type}
       -> {x : a} -> {xs : List a}
       -> {y : b} -> {ys : List b}
       -> (eq x y -> Void)
       -> (Subset eq (x :: xs) ys -> Void   )
       -> Subset eq (x :: xs) (y :: ys)
       -> Void
justNot f g (Keep prf rest) = f prf
justNot f g (Skip rest) = g rest

export
subset : {eq   : a -> b -> Type}
      -> (test : (x : a) -> (y : b) -> DecInfo err (eq x y))
      -> (this : List a)
      -> (that : List b)
              -> DecInfo (Error err) (Subset eq this that)
subset test [] []
  = Yes Empty

subset test [] (x :: xs)
  = Yes EmptyThis

subset test (x :: xs) []
  = No EmptyThat emptyThat

subset test (x :: xs) (y :: ys) with (test x y)
  subset test (x :: xs) (y :: ys) | (Yes prfHere) with (subset test xs ys)
    subset test (x :: xs) (y :: ys) | (Yes prfHere) | (Yes prfThere)
      = Yes (Keep prfHere prfThere)
    subset test (x :: xs) (y :: ys) | (Yes prfHere) | (No msgWhyNot prfWhyNot) with (subset test (x::xs) ys)
      subset test (x :: xs) (y :: ys) | (Yes prfHere) | (No msgWhyNot prfWhyNot) | (Yes prfThere)
        = Yes (Skip prfThere)
      subset test (x :: xs) (y :: ys) | (Yes prfHere) | (No msgWhyNotHere prfWhyNotHere) | (No msgWhyNotThere prfWhyNotThere)
        = No (FailThere msgWhyNotThere)
             (yesButNo prfWhyNotHere prfWhyNotThere)

  subset test (x :: xs) (y :: ys) | (No msgWhyNotHere prfWhyNotHere) with (subset test (x::xs) ys)
    subset test (x :: xs) (y :: ys) | (No msgWhyNotHere prfWhyNotHere) | (Yes prfThere)
      = Yes (Skip prfThere)
    subset test (x :: xs) (y :: ys) | (No msgWhyNotHere prfWhyNotHere) | (No msgWhyNotThere prfWhyNotThere)
      = No (FailThere msgWhyNotThere)
           (justNot prfWhyNotHere prfWhyNotThere)
