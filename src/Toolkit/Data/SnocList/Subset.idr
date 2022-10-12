|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.SnocList.Subset

import Data.SnocList
import Toolkit.Data.SnocList.Quantifiers
import Toolkit.Decidable.Informative

%default total

public export
data Subset : (eq   : a -> b -> Type)
           -> (this : SnocList a)
           -> (that : SnocList b)
                   -> Type
  where
    Empty : Subset eq [<] [<]

    Keep : {0 eq : a -> b -> Type}
        -> (prf  :        eq  x       y)
        -> (rest : Subset eq    xs      ys)
                -> Subset eq (xs :< x) (ys :< y)

    Skip : (rest : Subset eq xs  ys)
                -> Subset eq xs (ys :< y)

export
Uninhabited (Subset eq (xs :< x) [<]) where
  uninhabited prf impossible

namespace All

  export
  action : (compat : forall x, y. p y -> eq x y -> q x) ->
           All p ys -> Subset eq xs ys -> All q xs
  action compat pxs Empty = [<]
  action compat (pxs :< px) (Keep prf rest) = action compat pxs rest :< compat px prf
  action compat (pxs :< px) (Skip rest) = action compat pxs rest

export
Skips : {zs : SnocList b} -> Subset eq xs ys -> Subset eq xs (ys <+> zs)
Skips {zs = [<]} rest = rest
Skips {zs = (sx :< x)} rest = Skip (Skips rest)

namespace List

  export
  Skips : {zs : List b} -> Subset eq xs ys -> Subset eq xs (ys <>< zs)
  Skips {zs = []} rest = rest
  Skips {zs = z :: zs} rest = List.Skips (Skip rest)

export
EmptyThis : {xs : SnocList b} -> Subset eq [<] xs
EmptyThis {xs = [<]} = Empty
EmptyThis {xs = xs :< x} = Skip EmptyThis

export
trans : (forall x, y, z. eq x y -> eq y z -> eq x z) ->
        (Subset eq xs ys -> Subset eq ys zs -> Subset eq xs zs)
trans tr th Empty = th
trans tr (Keep prf1 th) (Keep prf2 ph) = Keep (tr prf1 prf2) (trans tr th ph)
trans tr (Skip th) (Keep prf ph) = Skip (trans tr th ph)
trans tr th (Skip ph) = Skip (trans tr th ph)

export
(<+>) : Subset {a, b} eq xs ys -> Subset eq as bs ->
       Subset eq (xs <+> as) (ys <+> bs)
th <+> Empty = th
th <+> Keep prf rest = Keep prf (th <+> rest)
th <+> Skip rest = Skip (th <+> rest)

public export
data Error : Type -> Type where
  EmptyThat : Error a
  Fail : a -> Error a
  FailThere : Error a -> Error a

yesButNo : {0 eq : a -> b -> Type}
        -> {0 x : a} -> {0 xs : SnocList a}
        -> {0 y : b} -> {0 ys : SnocList b}
        -> (h : Subset eq  xs        ys -> Void)
        -> (t : Subset eq (xs :< x)  ys -> Void)
             -> Subset eq (xs :< x) (ys :< y)
             -> Void
yesButNo h t (Keep prf rest) = h rest
yesButNo h t (Skip rest) = t rest

justNot : {0 eq : a -> b -> Type}
       -> {0 x : a} -> {0 xs : SnocList a}
       -> {0 y : b} -> {0 ys : SnocList b}
       -> (eq x y -> Void)
       -> (Subset eq (xs :< x) ys        -> Void)
       -> (Subset eq (xs :< x) (ys :< y) -> Void)
justNot f g (Keep prf rest) = f prf
justNot f g (Skip rest) = g rest

export
subset : {0 eq   : a -> b -> Type}
      -> (test : (x : a) -> (y : b) -> DecInfo err (eq x y))
      -> (this : SnocList a)
      -> (that : SnocList b)
              -> DecInfo (Error err) (Subset eq this that)
subset test [<] [<]
  = Yes Empty

subset test [<] (xs :< x)
  = Yes EmptyThis

subset test (xs :< x) [<]
  = No EmptyThat absurd

subset test (xs :< x) (ys :< y) with (test x y)
  _ | (Yes prfHere) with (subset test xs ys)
    _ | (Yes prfThere)
      = Yes (Keep prfHere prfThere)
    _ | (No msgWhyNot prfWhyNotHere) with (subset test (xs :< x) ys)
      _ | (Yes prfThere)
        = Yes (Skip prfThere)
      _ | (No msgWhyNotThere prfWhyNotThere)
        = No (FailThere msgWhyNotThere)
             (yesButNo prfWhyNotHere prfWhyNotThere)

  _ | (No msgWhyNotHere prfWhyNotHere) with (subset test (xs :< x) ys)
    _ | (Yes prfThere)
      = Yes (Skip prfThere)
    _ | (No msgWhyNotThere prfWhyNotThere)
      = No (FailThere msgWhyNotThere)
           (justNot prfWhyNotHere prfWhyNotThere)
