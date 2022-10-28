module Velo.Elaborator.Instantiate

import Data.SnocList.Quantifiers
import Data.List.Quantifiers
import Toolkit.Data.List.Member

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term

%default total

export
embed : Term [] ctxt ty -> Term metas ctxt ty
-- Cannot be bothered to implement a complicated identity function
embed = believe_me

substV :
  IsVar old ty ->
  Subst metas new old ->
  Term metas new ty
substV v [<] = absurd v
substV v@_ (sg :< t) with (view v)
  _ | Here = t
  _ | There v' = substV v' sg

export
subst :
  Term metas old ty ->
  Subst metas new old ->
  Term metas new ty

substS :
  Subst metas old ty ->
  Subst metas new old ->
  Subst metas new ty

substs :
  {0 tys : List Ty} ->
  All (Term metas old) tys ->
  Subst metas new old ->
  All (Term metas new) tys

subst (Var v) sg = substV v sg
subst (Met m sg') sg = Met m (substS sg' sg)
subst (Fun b) sg = Fun (subst b (mapProperty (rename shift) sg :< Var here))
subst (Call op ts) sg = Call op (substs ts sg)

substS [<] sg = [<]
substS (args :< arg) sg = substS args sg :< subst arg sg

substs [] sg = []
substs (t :: ts) sg = subst t sg :: substs ts sg

export
instantiate :
  Term metas ctxt ty ->
  (p : IsMember metas m) ->
  Term (drop p) m.metaScope m.metaType ->
  Term (drop p) ctxt ty

instantiates :
  {0 tys : List Ty} ->
  All (Term metas ctxt) tys ->
  (p : IsMember metas m) ->
  Term (drop p) m.metaScope m.metaType ->
  All (Term (drop p) ctxt) tys

instantiateS :
  Subst metas ctxt tys ->
  (p : IsMember metas m) ->
  Term (drop p) m.metaScope m.metaType ->
  Subst (drop p) ctxt tys

instantiate (Var v) p t = Var v
instantiate (Met mem sg) prf t with (hetDecEq prf mem)
  instantiate (Met mem sg) .(mem) t
    | Yes (Refl, Refl) = subst t (instantiateS sg mem t)
  instantiate (Met mem sg) prf t
    | No neq = Met (dropNeq neq) (instantiateS sg prf t)
instantiate (Fun b) p t = Fun (instantiate b p t)
instantiate (Call op ts) p t = Call op (instantiates ts p t)

instantiates [] p t = []
instantiates (arg :: args) p t = instantiate arg p t :: instantiates args p t

instantiateS [<] p t = [<]
instantiateS (args :< arg) p t = instantiateS args p t :< instantiate arg p t
