module PoC.Holes

import Toolkit.Data.List.Quantifiers
import Toolkit.Data.List.Pointwise
import Toolkit.Data.List.Subset

import Toolkit.DeBruijn.Variable
import Toolkit.DeBruijn.Context

import Decidable.Equality
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

namespace Raw

  data Check : Type
  data Synth : Type


  public export
  data Check : Type where
    Met : String -> Check
    Lam : String -> Check -> Check
    Emb : Synth -> Check

  public export
  data Synth : Type where
    Var : String -> Synth
    Cut : Check -> Ty -> Synth
    App : Synth -> Check -> Synth

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

  isVar : (ctxt : List Ty) ->
          All (\ _ => String) ctxt ->
          String ->
          Maybe (ty : Ty ** IsVar ctxt ty)
  isVar [] [] nm = Nothing
  isVar (ty :: tys) (x :: xs) nm = case decEq x nm of
    Yes Refl => pure (ty ** V 0 Here)
    No _ => bimap id shift <$> isVar tys xs nm

  steps : {dom : _} -> (holes : List (HoleIn (ctxt += dom))) ->
          (holes' : _ ** Pointwise (Stepped dom) holes holes')
  steps [] = ([] ** [])
  steps (MkHoleIn nm scp ty :: holes)
    = bimap (MkHoleIn nm (scp :< dom) ty ::) (MkHoleIn ::) (steps holes)

  merge : (holes1, holes2 : List (HoleIn ctxt)) ->
          Maybe (holes ** Merged holes holes1 holes2)
  merge [] holes2 = pure (holes2 ** NilL)
  merge holes1 [] = pure (holes1 ** NilR)
  merge (MkHoleIn nm1 scp1 ty1 :: holes1) (MkHoleIn nm2 scp2 ty2 :: holes2)
    = case decEq nm1 nm2 of
        Yes Refl => case decEq ty1 ty2 of
          No _ => Nothing
          Yes Refl => do (holes ** mg) <- merge holes1 holes2
                         pure (_ :: holes ** Both (MkConflit _ _) mg)
        No _ => if nm1 < nm2
          then do (holes ** mg) <- assert_total (merge holes1 (MkHoleIn nm2 scp2 ty2 :: holes2))
                  pure (_ :: holes ** ConL mg)
          else do (holes ** mg) <- assert_total (merge (MkHoleIn nm1 scp1 ty1 :: holes1) holes2)
                  pure (_ :: holes ** ConR mg)

  check : {ctxt : List Ty} ->
          All (\ _ => String) ctxt ->
          (ty : Ty) ->
          Check ->
          Maybe (holes : List (HoleIn ctxt) ** Holey ctxt holes ty)

  synth : {ctxt : List Ty} ->
          All (\ _ => String) ctxt ->
          Synth ->
          Maybe (ty : Ty ** holes : List (HoleIn ctxt) ** Holey ctxt holes ty)

  check scp ty (Met nm) = Just (_ ** Met nm)
  check scp ty (Lam x b)
    = do TyFunc dom cod <- isTyFunc ty
         (holes ** b) <- check {ctxt = dom :: ctxt} (x :: scp) cod b
         let (holes ** stepped) = steps holes
         pure (holes ** Lam stepped b)
  check scp ty (Emb s)
    = do (ty' ** holes ** tm) <- synth scp s
         case decEq ty ty' of
           Yes Refl => pure (holes ** tm)
           No _ => Nothing

  synth scp (Var v)
    = do (ty ** v) <- isVar _ scp v
         pure (ty ** [] ** Var v)
  synth scp (Cut t ty)
    = do (holes ** t) <- check scp ty t
         pure (ty ** holes ** t)
  synth scp (App f t)
    = do (ty ** holes1 ** f) <- synth scp f
         TyFunc dom cod <- isTyFunc ty
         (holes2 ** t) <- check scp dom t
         (holes ** mg) <- merge holes1 holes2
         pure (cod ** holes ** App f t mg)

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

  initInvariant : (ctxt : List Ty) -> (holes : List (HoleIn ctxt)) ->
                  (metas : List Meta ** Invariant ctxt holes metas)
  initInvariant ctxt [] = ([] ** [])
  initInvariant ctxt (MkHoleIn nm scp ty :: holes)
    = bimap (MkMeta nm (scp <>> ctxt) ty ::) (MkInstance Keeps ::) (initInvariant ctxt holes)

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
