module Toolkit.CoDeBruijn

import Decidable.Equality
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
