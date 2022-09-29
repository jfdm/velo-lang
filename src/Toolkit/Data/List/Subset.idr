|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Subset

import Toolkit.Decidable.Informative

%default total

public export
data Subset : (eq   : a -> b -> Type)
           -> (this : List a)
           -> (that : List b)
                   -> Type
  where
    Empty : Subset eq Nil Nil

    EmptyThis : Subset eq Nil xs

    Keep : {eq : a -> b -> Type}
        -> (prf  :        eq  x       y)
        -> (rest : Subset eq    xs      ys)
                -> Subset eq (x::xs) (y::ys)

    Skip : (rest : Subset eq xs     ys)
                -> Subset eq xs (y::ys)

export
Keeps : {xs : List a} -> Subset (===) xs xs
Keeps {xs = []} = Empty
Keeps {xs = x :: xs} = Keep Refl Keeps

export
Skips : {zs : SnocList b} -> Subset eq xs ys -> Subset eq xs (zs <>> ys)
Skips {zs = [<]} rest = rest
Skips {zs = (sz :< z)} rest = Skips (Skip rest)

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
