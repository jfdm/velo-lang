module Velo.IR.CoTerm

import Data.String
import Decidable.Equality

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

export
DecEq (CoTerm metas ctxt ty) where
  decEq = ?todo_deceq_coterm
