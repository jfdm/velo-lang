module Velo.IR.Term

import Data.String
import Decidable.Equality

import public Toolkit.Data.List.Member
import public Toolkit.Data.List.Quantifiers
import Toolkit.Data.SnocList.Thinning
import public Toolkit.Data.SnocList.Quantifiers
import public Toolkit.DeBruijn.Variable
import public Toolkit.Item

import Velo.Core
import Velo.Types
import Velo.IR.Common
import Velo.Elaborator.Common

import Velo.IR.Holey

import public Toolkit.DeBruijn.Renaming
import public Toolkit.DeBruijn.Substitution

%default total

------------------------------------------------------------------------
-- The type of well-scoped terms with meta variables

data Term  : (metas : List Meta) -> (ctxt : SnocList Ty) -> Ty -> Type

public export
Subst : (metas : List Meta) -> (ctxt : SnocList Ty) -> SnocList Ty -> Type
Subst metas ctxt = All (Term metas ctxt)

public export
data Term  : (metas : List Meta) -> (ctxt : SnocList Ty) -> Ty -> Type where
  Var : IsVar ctxt ty -> Term metas ctxt ty
  Met : IsMember metas m ->
        Subst metas ctxt m.metaScope ->
        Term metas ctxt m.metaType
  Fun : Term metas (ctxt :< a) b ->
        Term metas ctxt (TyFunc a b)
  Call : {tys : _} ->
         Prim tys ty ->
         All (Term metas ctxt) tys ->
         Term metas ctxt ty

------------------------------------------------------------------------
-- Smart constructor

export
toSubst : Thinning sx sy -> Subst metas sy sx
toSubst th = go th id where

  go : Thinning sa sb ->
       (forall ty. IsVar sb ty -> IsVar sc ty) ->
       Subst metas sc sa
  go Empty k = [<]
  go (Keep Refl th) k = go th (k . shift) :< Var (k here)
  go (Skip th) k = go th (k . shift)

------------------------------------------------------------------------
-- Renaming
public export
renames : (f : {0 ty : Ty} -> IsVar old ty -> IsVar new ty) ->
          Subst metas old tys ->
          Subst metas new tys

public export
Rename Ty (Term metas) where
  rename f (Var prf)
    = Var (f prf)

  rename f (Met {m} v sg)
    = Met v (renames f sg)

  rename f (Fun body)
    = Fun (rename (weaken f) body)

  rename f (Call p ts)
    = Call p (assert_total $ map (rename f) ts)

  embed = Var

renames f [<] = [<]
renames f (sg :< t) = renames f sg :< assert_total (rename f t)

------------------------------------------------------------------------
-- Substitution

substs : (f : {0 ty : Ty} -> IsVar old ty -> Term metas new ty) ->
         Subst metas old tys ->
         Subst metas new tys

public export
Substitute Ty (Term metas) where
  subst f (Var prf)
    = f prf

  subst f (Met v sg)
    = Met v (substs f sg)

  subst f (Fun body)
    = Fun (subst (weakens f) body)

  subst f (Call p ts)
    = Call p (assert_total $ map (subst f) ts)

substs f [<] = [<]
substs f (sg :< t) = substs f sg :< assert_total (subst f t)

------------------------------------------------------------------------
-- Decidable equality

export Injective Term.Var where injective Refl = Refl
export Biinjective Term.Met where biinjective Refl = (Refl, Refl)
export Biinjective Term.Call where biinjective Refl = (Refl, Refl)
export {tys : _} -> {p : Prim tys ty} -> Injective (Term.Call {tys} p) where injective Refl = Refl

export {0 x : a} -> {0 xs : List a} -> {0 p : a -> Type} ->
  Biinjective (All.(::) {p, x, xs}) where biinjective Refl = (Refl, Refl)

export {0 x : a} -> {0 xs : SnocList a} -> {0 p : a -> Type} ->
  Biinjective (All.(:<) {p, xs, x}) where biinjective Refl = (Refl, Refl)

namespace Term

  public export
  data HeadSim : (t : Term metas ctxt ty1) -> (u : Term metas ctxt ty2) -> Type where
    Var  : (v, w : _) -> HeadSim (Var v) (Var w)
    Met  : (v : IsMember metas m) -> (sg : Subst metas ctxt m.metaScope) ->
           (w : IsMember metas n) -> (sg' : Subst metas ctxt n.metaScope) ->
           HeadSim (Met v sg) (Met w sg')
    Fun  : (t, u : _) -> HeadSim (Fun t) (Fun u)
    Call : (tys, uys : List Ty) ->
           (p : Prim tys ty1) -> (ts : All (Term metas ctxt) tys) ->
           (q : Prim uys ty2) -> (us : All (Term metas ctxt) uys) ->
           HeadSim (Call p ts) (Call q us)

  public export
  headSim : (t : Term metas ctxt ty1) -> (u : Term metas ctxt ty2) ->
            Maybe (HeadSim t u)
  headSim (Var _) (Var _) = pure (Var _ _)
  headSim (Met _ _) (Met _ _) = pure (Met _ _ _ _)
  headSim (Fun _) (Fun _) = pure (Fun _ _)
  headSim (Call _ _) (Call _ _) = pure (Call _ _ _ _ _ _)
  headSim _ _ = Nothing

  export
  headSimFullDiag : (t : Term metas ctxt ty) -> Not (headSim t t === Nothing)
  headSimFullDiag (Var _) = absurd
  headSimFullDiag (Met _ _) = absurd
  headSimFullDiag (Fun _) = absurd
  headSimFullDiag (Call _ _) = absurd

  public export
  decEqTerm : (t, u : Term metas ctxt ty) -> Dec (t === u)
  public export
  decEqTerms : {0 tys : List Ty} -> (ts, us : All (Term metas ctxt) tys) -> Dec (ts === us)
  public export
  decEqSubst : (sg, sg' : Subst metas ctxt tys) -> Dec (sg === sg')
  public export
  decEqHeadSim : {0 t, u : Term metas ctxt ty} -> HeadSim t u -> Dec (t === u)

  decEqHeadSim (Var v w) = decEqCong (decEq v w)

  decEqHeadSim (Met {m = MkMeta {}} {n = MkMeta {}} v sg w sg') with (hetDecEq v w)
    _ | No neq = No (\ Refl => neq (Refl, Refl))
    decEqHeadSim (Met {m = MkMeta {}} {n = MkMeta {}} v sg v sg')
      | Yes (Refl, Refl) with (decEqSubst sg sg')
        _ | No neq = No (\ eq => neq (snd $ biinjective eq))
        _ | Yes eq = Yes (cong (Met v) eq)

  decEqHeadSim (Fun t u) with (decEqTerm t u)
    _ | Yes eq = Yes (cong Fun eq)
    _ | No neq = No (\case Refl => neq Refl)

  decEqHeadSim (Call tys uys p ts q us) with (hetDecEq p q)
    decEqHeadSim (Call tys .(tys) p ts .(p) us) | Yes (Refl, Refl, Refl)
      = decEqCong (decEqTerms ts us)
    _ | No neq = No (\case Refl => neq (Refl, Refl, Refl))

  decEqTerm t u with (headSim t u) proof hdSim
    decEqTerm t u | Nothing = No (\ Refl => headSimFullDiag _ hdSim)
    decEqTerm t u | Just prf = decEqHeadSim prf

  decEqTerms [] [] = Yes Refl
  decEqTerms (t :: ts) (u :: us) = decEqCong2 (decEqTerm t u) (decEqTerms ts us)

  decEqSubst [<] [<] = Yes Refl
  decEqSubst (sg :< t) (sg' :< t') = decEqCong2 (decEqSubst sg sg') (decEqTerm t t')

public export
DecEq (Term metas ctxt ty) where
  decEq = decEqTerm

export
{metas : _} -> Show (Term metas ctxt ty) where
  show (Var v) = show v
  show (Met m sg) = let (MkMeta nm _ _ ** eq) = lookup m in nm
  show (Fun b) = "\\. " ++ show b
  show (Call op []) = show op
  show (Call op ts) = "(" ++ show op ++ call ts ++ ")" where

    call : {0 tys : List Ty} -> All (Term metas ctxt) tys -> String
    call [] = ""
    call (t :: ts) = " " ++ show t ++ call ts
