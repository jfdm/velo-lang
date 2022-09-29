module PoC.Holes

import Toolkit.Data.List.Pointwise
import Toolkit.Data.List.Subset

import Toolkit.DeBruijn.Variable
import Toolkit.DeBruijn.Context

import Data.DPair

import Velo.Types

%default total

Name : Type
Name = String

record HoleIn (ctxt : List Ty) where
  constructor MkHoleIn
  holeName : Name
  localExtension : SnocList Ty
  holeType : Ty

record Meta where
  constructor MkMeta
  metaName : Name
  metaScope : List Ty
  metaType : Ty

Thinning : (xs, ys : List a) -> Type
Thinning = Subset (===)

namespace Holey

  public export
  data Stepped : (a : Ty) -> HoleIn (ctxt += a) -> HoleIn ctxt -> Type where
    MkHoleIn : Stepped a (MkHoleIn nm ext ty) (MkHoleIn nm (ext :< a) ty)

  public export
  data Conflict : (h, h1, h2 : HoleIn ctxt) -> Type where
    MkConflit : (nm : Name) -> (ty : Ty) -> {ext1, ext2 : _} ->
                Conflict (MkHoleIn nm [<] ty) (MkHoleIn nm ext1 ty) (MkHoleIn nm ext2 ty)

  public export
  data Merged : (holes, holes1, holes2 : List (HoleIn ctxt)) -> Type where
    NilL : Merged holes [] holes
    NilR : Merged holes holes []
    Both : Conflict h h1 h2 ->
           Merged holes holes1 holes2 ->
           Merged (h :: holes) (h1 :: holes1) (h2 :: holes2)
    ConL : -- invariant: h1.name < h2.name
           Merged holes holes1 holes2 ->
           Merged (h1 :: holes) (h1 :: holes1) holes2
    ConR : -- invariant: h1.name > h2.name
           Merged holes holes1 holes2 ->
           Merged (h2 :: holes) holes1 (h2 :: holes2)

  public export
  data Holey : (ctxt : List Ty) -> List (HoleIn ctxt) -> Ty -> Type where
    Var : IsVar ctxt ty -> Holey ctxt [] ty
    Met : (nm : Name) -> Holey ctxt [MkHoleIn nm [<] ty] ty
    Lam : Pointwise (Stepped a) holes1 holes2 ->
          Holey (ctxt += a) holes1 b ->
          Holey ctxt holes2 (TyFunc a b)
    App : Holey ctxt holes1 (TyFunc a b) ->
          Holey ctxt holes2 a ->
          Merged holes holes1 holes2 ->
          Holey ctxt holes b

namespace WellScoped

  public export
  data WScoped : (ctxt : List Ty) -> (metas : List Meta) -> Ty -> Type where
    Var : IsVar ctxt ty -> WScoped ctxt metas ty
    Met : IsVar metas m -> Thinning m.metaScope ctxt -> WScoped ctxt metas m.metaType
    Lam : WScoped (ctxt += a) metas b -> WScoped ctxt metas (TyFunc a b)
    App : WScoped ctxt metas (TyFunc a b) ->
          WScoped ctxt metas a ->
          WScoped ctxt metas b

  public export
  data Instance : (ctxt : List Ty) -> HoleIn ctxt -> Meta -> Type where
    MkInstance : Thinning scp (ext <>> ctxt) ->
                 Instance ctxt (MkHoleIn nm ext ty) (MkMeta nm scp ty)

  public export
  data Invariant : (ctxt : List Ty) -> List (HoleIn ctxt) -> List Meta -> Type where
    Nil  : Invariant ctxt [] []
    Skip : Invariant ctxt holes metas ->
           Invariant ctxt holes (m :: metas)
    (::) : Instance ctxt h m ->
           Invariant ctxt holes metas ->
           Invariant ctxt (h :: holes) (m :: metas)

  Skips : {metas : List Meta} -> Invariant ctxt [] metas
  Skips {metas = []} = []
  Skips {metas = m :: metas} = Skip Skips

  namespace Meta
    export
    wscoped : Invariant ctxt [MkHoleIn nm [<] ty] metas ->
              Exists (\ scp => (IsVar metas (MkMeta nm scp ty), Thinning scp ctxt))
    wscoped (Skip inv)
      = let Evidence scp (v, th) = wscoped inv in Evidence scp (shift v, th)
    wscoped (MkInstance th :: _) = Evidence ? (V 0 Here, th)

  step : Stepped a h h1 -> Instance ctxt h1 m -> Instance (ctxt += a) h m
  step MkHoleIn (MkInstance th) = MkInstance th

  steps : Pointwise (Stepped a) holes1 holes ->
         Invariant ctxt holes metas ->
         Invariant (ctxt += a) holes1 metas
  steps [] [] = []
  steps pw (Skip inv) = Skip (steps pw inv)
  steps (stp :: xs) (inst :: inv) = step stp inst :: steps xs inv

  unconflict : Conflict h h1 h2 ->
               Instance ctxt h m ->
               (Instance ctxt h1 m, Instance ctxt h2 m)
  unconflict (MkConflit nm ty) (MkInstance th)
    = (MkInstance (Skips th), MkInstance (Skips th))

  unmerge : {metas : _} ->
            Merged holes holes1 holes2 ->
            Invariant ctxt holes metas ->
            (Invariant ctxt holes1 metas, Invariant ctxt holes2 metas)
  unmerge mg (Skip inv) = bimap Skip Skip (unmerge mg inv)
  unmerge NilL inv = (Skips, inv)
  unmerge NilR inv = (inv, Skips)
  unmerge (Both cflt mg) (inst :: inv)
    = let (inst1, inst2) = unconflict cflt inst in
      bimap (inst1 ::) (inst2 ::) (unmerge mg inv)
  unmerge (ConL mg) (inst :: inv) = bimap (inst ::) Skip (unmerge mg inv)
  unmerge (ConR mg) (inst :: inv) = bimap Skip (inst ::) (unmerge mg inv)

  wscoped : {metas : _} ->
            Holey ctxt holes ty ->
            Invariant ctxt holes metas ->
            WScoped ctxt metas ty
  wscoped (Var x) inv = Var x
  wscoped (Met nm) inv = let Evidence _ (v, th) = wscoped inv in Met v th
  wscoped (Lam pw b) inv = Lam (wscoped b (steps pw inv))
  wscoped (App f t mg) inv =
    let (inv1, inv2) = unmerge mg inv in
    App (wscoped f inv1) (wscoped t inv2)
