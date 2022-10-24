module Velo.IR.CoTerm

import Data.String
import Decidable.Equality

import Toolkit.Data.Comparison.Informative
import public Toolkit.Data.List.Member
import Toolkit.Data.List.Pointwise
import public Toolkit.Data.List.Quantifiers
import Toolkit.Data.SnocList.Quantifiers
import Toolkit.Data.SnocList.Thinning

import public Toolkit.CoDeBruijn.Variable
import public Toolkit.CoDeBruijn.Binding
import public Toolkit.CoDeBruijn

import Velo.Core
import Velo.Types
import Velo.IR.Common

%default total

------------------------------------------------------------------------
-- The type of well-scoped terms using de Bruijn indices with meta variables

data CoTerms : (metas : List Meta) -> (ctxt : SnocList Ty) -> List Ty -> Type
data CoSubst : (metas : List Meta) -> (ctxt : SnocList Ty) -> SnocList Ty -> Type

public export
data CoTerm : (metas : List Meta) -> (ctxt : SnocList Ty) -> Ty -> Type where
  Var  : IsVar ctxt ty -> CoTerm metas ctxt ty
  Met  : IsMember metas m ->
         CoSubst metas ctxt m.metaScope ->
         CoTerm metas ctxt m.metaType
  Fun  : Binding (\ ctxt => CoTerm metas ctxt b) a ctxt -> CoTerm metas ctxt (TyFunc a b)
  Call : {tys : _} -> Prim tys ty ->
         CoTerms metas ctxt tys ->
         CoTerm metas ctxt ty

public export
data CoTerms : (metas : List Meta) -> (ctxt : SnocList Ty) -> List Ty -> Type where
  Nil  : CoTerms metas [<] []
  Cons : Relevant
           (\ ctxt => CoTerm metas ctxt ty)
           (\ ctxt => CoTerms metas ctxt tys)
           ctxt ->
         CoTerms metas ctxt (ty :: tys)

public export
data CoSubst : (metas : List Meta) -> (ctxt : SnocList Ty) -> SnocList Ty -> Type where
  Lin  : CoSubst metas [<] [<]
  Snoc : Relevant
           (\ ctxt => CoSubst metas ctxt tys)
           (\ ctxt => CoTerm metas ctxt ty)
           ctxt ->
         CoSubst metas ctxt (tys :< ty)

export Injective Var where injective Refl = Refl
export Injective Fun where injective Refl = Refl
export {tys : _} -> {op : Prim tys _} -> Injective (Call {tys} op) where injective Refl = Refl
export {m : IsMember ms _} -> Injective (Met m) where injective Refl = Refl

export Injective Cons where injective Refl = Refl
export Injective Snoc where injective Refl = Refl

namespace CoTerm

  public export
  tag : CoTerm metas ctxt t -> Nat
  tag (Var _) = 0
  tag (Met _ _) = 1
  tag (Fun _) = 2
  tag (Call _ _) = 3

  public export
  size : CoTerm metas ctxt t -> Nat
  sizes : CoTerms metas ctxt t -> Nat

  size (Fun (K b)) = S (size b)
  size (Fun (R _ b)) = S (size b)
  size (Call op ts) = S (sizes ts)
  size _ = 1

  sizes [] = 0
  sizes (Cons (MkRelevant t _ ts)) = size t + sizes ts

  public export
  data HeadSim : (t : CoTerm metas ctxt ty1) -> (u : CoTerm metas ctxt ty2) -> Type where
    Var  : (v, w : _) -> HeadSim (Var v) (Var w)
    Met  : (v : IsMember metas m) -> (sg : CoSubst metas ctxt m.metaScope) ->
           (w : IsMember metas n) -> (sg' : CoSubst metas ctxt n.metaScope) ->
           HeadSim (Met v sg) (Met w sg')
    Fun  : (t, u : _) -> HeadSim (Fun t) (Fun u)
    Call : (tys, uys : List Ty) ->
           (p : Prim tys ty1) -> (ts : CoTerms metas ctxt tys) ->
           (q : Prim uys ty2) -> (us : CoTerms metas ctxt uys) ->
           HeadSim (Call p ts) (Call q us)

  public export
  headSim : (t : CoTerm metas ctxt ty1) -> (u : CoTerm metas ctxt ty2) ->
            Maybe (HeadSim t u)
  headSim (Var _) (Var _) = pure (Var _ _)
  headSim (Met _ _) (Met _ _) = pure (Met _ _ _ _)
  headSim (Fun _) (Fun _) = pure (Fun _ _)
  headSim (Call _ _) (Call _ _) = pure (Call _ _ _ _ _ _)
  headSim _ _ = Nothing

  export
  headSimFullDiag : (t : CoTerm metas ctxt ty) -> Not (headSim t t === Nothing)
  headSimFullDiag (Var _) = absurd
  headSimFullDiag (Met _ _) = absurd
  headSimFullDiag (Fun _) = absurd
  headSimFullDiag (Call _ _) = absurd

  public export
  decEqCoTerm : (t, u : CoTerm metas ctxt ty) -> Dec (t === u)
  public export
  decEqCoTerms : {0 tys : List Ty} -> (ts, us : CoTerms metas ctxt tys) -> Dec (ts === us)
  public export
  decEqCoSubst : (sg, sg' : CoSubst metas ctxt tys) -> Dec (sg === sg')
  public export
  decEqHeadSim : {0 t, u : CoTerm metas ctxt ty} -> HeadSim t u -> Dec (t === u)

  public export
  DecEq (CoTerm metas ctxt ty) where
    decEq = decEqCoTerm

  public export
  DecEq (CoTerms metas ctxt tys) where
    decEq = decEqCoTerms

  public export
  DecEq (CoSubst metas ctxt tys) where
    decEq = decEqCoSubst

  decEqCoTerm t u with (headSim t u) proof sim
    _ | Just prf = decEqHeadSim prf
    _ | Nothing = No (\ Refl => headSimFullDiag _ sim)

  decEqHeadSim (Var v w) = decEqCong (decEq v w)
  decEqHeadSim (Met {m = m@(MkMeta{})} p sg {n = n@(MkMeta{})} q sg') with (hetDecEq p q)
    decEqHeadSim (Met {m = m@(MkMeta{})} p sg {n = n@(MkMeta{})} q sg')
       | No neq = No (\ Refl => neq (Refl, Refl))
    decEqHeadSim (Met {m = m@(MkMeta{})} p sg {n = n@(MkMeta{})} p sg')
       | Yes (Refl, Refl) = decEqCong (assert_total $ decEqCoSubst sg sg')
  decEqHeadSim (Fun b c) = decEqCong (decEq b c)
  decEqHeadSim (Call tys uys p ts q us) with (hetDecEq p q)
    decEqHeadSim (Call tys uys p ts q us)
      | No nprf = No (\ Refl => nprf (Refl, Refl, Refl))
    decEqHeadSim (Call tys tys p ts p us)
      | Yes (Refl, Refl, Refl) = decEqCong (decEqCoTerms ts us)

  decEqCoTerms [] [] = Yes Refl
  decEqCoTerms (Cons tts) (Cons uus) = decEqCong (assert_total $ decEq tts uus)

  decEqCoSubst [<] [<] = Yes Refl
  decEqCoSubst (Snoc sgt) (Snoc sgt') = decEqCong (decEq sgt sgt')

  public export
  Eq (CoTerm metas ctxt ty) where
    t == u = case decEq t u of
      Yes _ => True
      No _ => False

  Eq (CoTerms metas ctxt ty) where
    t == u = case decEq t u of
      Yes _ => True
      No _ => False

  Eq (CoSubst metas ctxt ty) where
    t == u = case decEq t u of
      Yes _ => True
      No _ => False

  compareCoTerm : (t, u : CoTerm metas ctxt ty) -> Ordering
  compareCoTerms : {0 tys : List Ty} -> (ts, us : CoTerms metas ctxt tys) -> Ordering
  compareCoSubst : (sg, sg' : CoSubst metas ctxt tys) -> Ordering
  compareHeadSim : {0 t, u : CoTerm metas ctxt ty} -> HeadSim t u -> Ordering

  public export
  Ord (CoTerm metas ctxt ty) where compare = compareCoTerm
  Ord (CoTerms metas ctxt tys) where compare = compareCoTerms
  Ord (CoSubst metas ctxt tys) where compare = compareCoSubst

  compareHeadSim (Var Here Here) = EQ
  compareHeadSim (Met {m = MkMeta{}} {n = MkMeta{}} p sg q sg') with (cmp p q)
    _ | LT = LT
    _ | GT = GT
    compareHeadSim (Met {m = MkMeta{}} {n = MkMeta{}} p sg .(p) sg')
      | EQ = compare sg sg'
  compareHeadSim (Fun b c) = compare b c
  compareHeadSim (Call tys uys p ts q us) with (cmp p q)
    _ | LT = LT
    compareHeadSim (Call tys .(tys) p ts .(p) us) | EQ = compareCoTerms ts us
    _ | GT = GT

  compareCoTerm t u with (headSim t u)
    _ | Nothing = compare (tag t) (tag u)
    _ | Just prf = compareHeadSim prf

  compareCoTerms [] [] = EQ
  compareCoTerms (Cons tts) (Cons uus) = assert_total (compare tts uus)

  compareCoSubst [<] [<] = EQ
  compareCoSubst (Snoc tst) (Snoc usu) = assert_total (compare tst usu)
