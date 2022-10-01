module PoC.CSE

import Control.Function
import Decidable.Equality
import Data.Maybe
import Data.String

import Toolkit.Data.List.Quantifiers
import Toolkit.Data.List.Thinning

import Toolkit.DeBruijn.Variable
import Toolkit.DeBruijn.Context

import Toolkit.CoDeBruijn.Variable
import Toolkit.CoDeBruijn.Binding
import Toolkit.CoDeBruijn

import Velo.Types

%default total

Scoped : Type -> Type
Scoped a = List a -> a -> Type

namespace DeBruijn

  %hide CoDeBruijn.Variable.IsVar

  public export
  data Tm : Scoped Ty where
    V : IsVar g s -> Tm g s
    A : {s : Ty} -> Tm g (TyFunc s t) -> Tm g s -> Tm g t
    L : Tm (g += s) t -> Tm g (s `TyFunc` t)

  namespace Tm
    export
    thin : Tm g s -> Thinning g g' -> Tm g' s
    thin (V v) th = V (thin v th)
    thin (A f t) th = A (thin f th) (thin t th)
    thin (L b) th = L (thin b (Keep Refl th))

  export
  CONST : Tm [] (TyFunc TyBool $ TyFunc TyBool TyBool)
  CONST = L (L (V (shift here)))

  export
  ID : Tm [] (TyFunc TyBool TyBool)
  ID = L (V here)

  export
  SKIP : Tm [] (TyFunc TyBool $ TyFunc TyBool TyBool)
  SKIP = L (L (V here))

  export
  CONSTS : Tm [] (TyFunc TyBool $ TyFunc TyBool TyBool)
  CONSTS = A (A (A (L $ L $ L $ thin CONST none) CONST) CONST) CONST


namespace CoDeBruijn

  %hide DeBruijn.Variable.IsVar
  %hide DeBruijn.Tm
  %hide DeBruijn.V
  %hide DeBruijn.A
  %hide DeBruijn.L

  %unhide CoDeBruijn.Variable.IsVar

  public export
  data Tm : Scoped Ty where
    V : IsVar g s -> Tm g s
    A : {s : Ty} -> Relevant (`Tm` (s `TyFunc` t)) (`Tm` s) g -> Tm g t
    L : Binding (`Tm` t) s g -> Tm g (s `TyFunc` t)

  public export
  appDomain : {s : _} -> Tm g s -> Ty
  appDomain (A {s = dom} _) = dom
  appDomain _ = s

  export Injective (V {s, g}) where injective Refl = Refl
  export {s : Ty} -> Injective (A {s, t, g}) where injective Refl = Refl
  export Injective (L {s, t, g}) where injective Refl = Refl

  export Uninhabited (V v === A {s, t, g} ft) where uninhabited Refl impossible
  export Uninhabited (A {s, t, g} ft === V v) where uninhabited Refl impossible
  export Uninhabited (V v === L {s, t, g} ft) where uninhabited Refl impossible
  export Uninhabited (L {s, t, g} ft === V v) where uninhabited Refl impossible

  export Uninhabited (L {s, t, g} b === A ft) where uninhabited Refl impossible
  export Uninhabited (A ft === L {s, t, g} b) where uninhabited Refl impossible

  export
  DecEq (Tm g s) where
    decEq (V v) (V w) = decEqCong (decEq v w)
    decEq (V _) (A _) = No absurd
    decEq (A _) (V _) = No absurd
    decEq (V _) (L _) = No absurd
    decEq (L _) (V _) = No absurd
    decEq (A {s = s@_} p) (A {s = s'} q) with (decEq s s')
      _ | Yes Refl = decEqCong ?azrpjgzj
      _ | No neq = No (neq . cong appDomain)
    decEq (A _) (L _) = No absurd
    decEq (L _) (A _) = No absurd
    decEq (L b) (L c) = decEqCong (decEq b c)

%unhide DeBruijn.Variable.IsVar
%unhide DeBruijn.Tm
%unhide DeBruijn.V
%unhide DeBruijn.A
%unhide DeBruijn.L

namespace IsVar

  export
  coDeBruijn : {g : _} ->
               DeBruijn.Variable.IsVar g s ->
               Diamond (`CoDeBruijn.Variable.IsVar` s) g
  coDeBruijn v@_ with (view v)
    coDeBruijn {g = _ :: _} v@_ | Here = MkDiamond (Keep Refl none) Here
    coDeBruijn {g = _ :: _} v@_ | There w = Skip (coDeBruijn w)

  export
  deBruijn : CoDeBruijn.Variable.IsVar g s ->
             DeBruijn.Variable.IsVar g s
  deBruijn Here = here

namespace Tm

  export
  coDeBruijn : {g, s : _} -> DeBruijn.Tm g s -> Diamond (`CoDeBruijn.Tm` s) g
  coDeBruijn (V v) = V <$> coDeBruijn v
  coDeBruijn (A f t) = A <$> relevant (coDeBruijn f) (coDeBruijn t)
  coDeBruijn (L b) = L <$> bind (coDeBruijn b)

  export
  deBruijn : CoDeBruijn.Tm g s -> Thinning g g' -> DeBruijn.Tm g' s
  deBruijn (V v) th = V (thin (deBruijn v) th)
  deBruijn (A (MkRelevant {th = left} {ph = right} f _ t)) th
    = A (deBruijn f (left <.> th)) (deBruijn t (right <.> th))
  deBruijn (L (K b)) th = L (deBruijn b (Skip th))
  deBruijn (L (R s b)) th = L (deBruijn b (Keep Refl th))

namespace CoDeBruijn

  export
  coDeBruijn : {s : _} -> DeBruijn.Tm [] s  -> CoDeBruijn.Tm [] s
  coDeBruijn t = let (MkDiamond Empty tm) = coDeBruijn t in tm

  export
  CONST : CoDeBruijn.Tm [] (TyFunc TyBool $ TyFunc TyBool TyBool)
  CONST = coDeBruijn DeBruijn.CONST

  export
  SKIP : CoDeBruijn.Tm [] (TyFunc TyBool $ TyFunc TyBool TyBool)
  SKIP = coDeBruijn DeBruijn.SKIP

  export
  ID : CoDeBruijn.Tm [] (TyFunc TyBool TyBool)
  ID = coDeBruijn DeBruijn.ID

  export
  CONSTS : CoDeBruijn.Tm [] (TyFunc TyBool $ TyFunc TyBool TyBool)
  CONSTS = coDeBruijn DeBruijn.CONSTS

namespace Tm

  ||| abstract here (provided things match up)
  abstractH : {g, g', ctx, s, t : _} ->
              DeBruijn.Variable.IsVar (g' ++ g) s -> Diamond (`CoDeBruijn.Tm` s) g ->
              Diamond (`CoDeBruijn.Tm` t) (ctx ++ g) ->
              Maybe (Diamond (`CoDeBruijn.Tm` t) (ctx ++ (g' ++ g)))
  abstractH v se@(MkDiamond {support = xs@_} th se'@_) tm@(MkDiamond {support = ys} ph tm')
    with (decEq s t)
    _ | No p = Nothing
    _ | Yes Refl with (decEq xs ys)
      _ | No p = Nothing
      _ | Yes Refl with (decEq se' tm')
        _ | Yes Refl = pure (coDeBruijn (V (shifts v)))
        _ | No p = Nothing

  first : {xs : List a} ->
          ({x : a} -> DeBruijn.Variable.IsVar (xs ++ ys) x -> p x -> Maybe b) ->
          All p xs -> Maybe b
  first p [] = Nothing
  first p (x :: xs) = p here x <|> first (p . shift) xs

  export
  abstractR : {g, g', ctx, t : _} ->
              All (\ s => Diamond (`CoDeBruijn.Tm` s) g) g' ->
              Diamond (`CoDeBruijn.Tm` t) (ctx ++ g) ->
              Diamond (`CoDeBruijn.Tm` t) (ctx ++ (g' ++ g))
  abstractR ses tm = case first (\ v, se => abstractH v se tm) ses of
    Just tm => tm
    Nothing => case tm of
      (MkDiamond th (A (MkRelevant {th = left} {ph = right} f cover t))) =>
        let f = assert_total $ abstractR ses (MkDiamond (left <.> th) f) in
        let t = assert_total $ abstractR ses (MkDiamond (right <.> th) t) in
        let ft = A <$> relevant f t in
        ft
      (MkDiamond th (L (K b))) =>
        (L . K) <$> abstractR ses (MkDiamond th b)
      (MkDiamond th (L (R x b))) =>
        L <$> bind (abstractR {ctx = x :: ctx} ses (MkDiamond (Keep Refl th) b))
      _ => thin tm (ones ++ Skips ones {zs = g'})

  export
  CSE : DeBruijn.Tm [] (TyFunc TyBool $ TyFunc TyBool TyBool)
  CSE =
    let tm = abstractR {ctx = []} [MkDiamond Empty CONST] (MkDiamond Empty CONSTS) in
    let MkDiamond th f = L <$> bind tm in
    A (deBruijn f th) CONST

{-
main : IO ()
main = do
  putStrLn "CONST  : \{show $ DeBruijn.CONST}"
  putStrLn "CONSTS : \{show $ DeBruijn.CONSTS}"
  putStrLn "CSE    : \{show $ CSE}"
-}
