module Toolkit.CoDeBruijn

import Control.Function
import Decidable.Equality
import Toolkit.Data.Comparison.Informative
import Toolkit.Data.SnocList.Thinning
import Toolkit.CoDeBruijn.Binding

%default total

namespace Pair

  ||| A relevant pair is a pair that takes two values indexed by their
  ||| strict support, and returns a pair indexed by its strict support
  public export
  data Relevant : (t, p : SnocList a -> Type) -> (xs : SnocList a) -> Type where
    MkRelevant : {xs1, xs2 : _} ->
                 {th : Thinning xs1 xs} -> {ph : Thinning xs2 xs} ->
                 t xs1 -> Cover th ph -> p xs2 -> Relevant t p xs

  public export
  (forall xs. DecEq (t xs)) => (forall xs. DecEq (p xs)) => DecEq (Relevant t p xs) where
     decEq (MkRelevant {th = left1, ph = right1} l1 c1 r1)
           (MkRelevant {th = left2, ph = right2} l2 c2 r2)
       with (eqTh left1 left2) | (eqTh right1 right2)
       decEq (MkRelevant {th = left1, ph = right1} l1 c1 r1)
             (MkRelevant {th = left1, ph = right1} l2 c2 r2)
         | Yes (Refl, Refl) | Yes (Refl, Refl) with (decEq l1 l2) | (decEq r1 r2)
         decEq (MkRelevant {th = left1, ph = right1} l1 c1 r1)
               (MkRelevant {th = left1, ph = right1} l1 c2 r1)
           | Yes (Refl, Refl) | Yes (Refl, Refl)
           | Yes Refl | Yes Refl = Yes (rewrite irrelevantCover c1 c2 in Refl)
         _ | No neq1 | _ = No (\ Refl => neq1 Refl)
         _ | _ | No neq2 = No (\ Refl => neq2 Refl)
       _ | No neq1 | _ = No (\ Refl => neq1 (Refl, Refl))
       _ | _ | No neq2 = No (\ Refl => neq2 (Refl, Refl))

  public export
  (forall xs. Eq (t xs)) => (forall xs. Eq (p xs)) => Eq (Relevant t p xs) where
    (MkRelevant {th = left1, ph = right1} l1 c1 r1)
      == (MkRelevant {th = left2, ph = right2} l2 c2 r2)
      with (cmp left1 left2)
      (MkRelevant {th = left1, ph = right1} l1 c1 r1)
        == (MkRelevant {th = left1, ph = right2} l2 c2 r2)
        | EQ with (cmp right1 right2)
          (MkRelevant {th = left1, ph = right1} l1 c1 r1)
            == (MkRelevant {th = left1, ph = right1} l2 c2 r2)
              | EQ | EQ = (l1, r1) == (l2, r2)
          _ | _ = False
      _ | _ = False

  public export
  (forall xs. Ord (t xs)) => (forall xs. Ord (p xs)) => Ord (Relevant t p xs) where
    compare
      (MkRelevant {th = left1, ph = right1} l1 c1 r1)
      (MkRelevant {th = left2, ph = right2} l2 c2 r2)
      with (cmp left1 left2)
      _ | LT = LT
      _ | GT = GT
      compare
        (MkRelevant {th = left1, ph = right1} l1 c1 r1)
        (MkRelevant {th = left1, ph = right2} l2 c2 r2)
        | EQ with (cmp right1 right2)
          _ | LT = LT
          _ | GT = GT
          compare
            (MkRelevant {th = left1, ph = right1} l1 c1 r1)
            (MkRelevant {th = left1, ph = right1} l2 c2 r2)
              | EQ | EQ = compare (l1, r1) (l2, r2)


namespace Diamond

  ||| A relevant type can be embedded in a wider scope using the Diamond
  ||| constructor. The name is a reference to modal logic's ◇.
  public export
  record Diamond {a : Type} (t : SnocList a -> Type) (xs : SnocList a) where
    constructor MkDiamond
    {support : SnocList a}
    selection : Thinning {a} support xs
    selected  : t support

  export
  thin : Diamond t xs -> Thinning xs ys -> Diamond t ys
  thin (MkDiamond th tm) ph = MkDiamond (th <.> ph) tm

  -- TODO: generalise to arbitrary thinning?
  export
  thick : Diamond t (xs :< x) -> Maybe (Diamond t xs)
  thick (MkDiamond (Keep {}) v) = Nothing
  thick (MkDiamond (Skip th) v) = Just (MkDiamond th v)

  export
  Skip : Diamond t xs -> Diamond {a} t (xs :< x)
  Skip (MkDiamond sel t) = MkDiamond (Skip sel) t

  export
  (<$>) : (forall xs. t xs -> u xs) -> Diamond t xs -> Diamond u xs
  f <$> MkDiamond sel t = MkDiamond sel (f t)

  export
  bind : Diamond p (g :< s) -> Diamond (Binding p s) g
  bind (MkDiamond (Skip sel) b) = MkDiamond sel (K b)
  bind (MkDiamond (Keep Refl sel) b) = MkDiamond sel (R _ b)

  export
  relevant : {g : _} -> Diamond t g -> Diamond p g -> Diamond (Relevant t p) g
  relevant (MkDiamond th t) (MkDiamond ph p)
    = let (MkJoin middle cover) = join th ph in
      MkDiamond middle (MkRelevant t cover p)

  export
  {0 a : _} -> {0 t : SnocList a -> Type} ->
  {0 xs : SnocList a} -> {g : SnocList a} ->
  {th : Thinning g xs} ->
  Injective (MkDiamond {t, xs, support = g} th) where injective Refl = Refl

  public export
  (forall xs. DecEq (t xs)) => DecEq (Diamond t xs) where
    decEq (MkDiamond th t) (MkDiamond ph u) with (eqTh th ph)
      _ | No neq = No (\ Refl => neq (Refl, Refl))
      decEq (MkDiamond th t) (MkDiamond .(th) u)
        | Yes (Refl, Refl) = decEqCong (decEq t u)

  public export
  (forall xs. Eq (t xs)) => Eq (Diamond t xs) where
    MkDiamond th t == MkDiamond ph u with (eqTh th ph)
      _ | No neq = False
      MkDiamond th t == MkDiamond .(th) u
        | Yes (Refl, Refl) = t == u

  public export
  (forall xs. Ord (t xs)) => Ord (Diamond t xs) where
    compare (MkDiamond th t) (MkDiamond ph u) with (cmp th ph)
      _ | LT = LT
      _ | GT = GT
      compare (MkDiamond th t) (MkDiamond .(th) u)
        | EQ = compare t u
