module Velo.Elaborator.CoDeBruijn

import Toolkit.CoDeBruijn
import Toolkit.CoDeBruijn.Variable
import Toolkit.DeBruijn.Variable

import Toolkit.Data.SnocList.Thinning

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term
import Velo.IR.CoTerm

%default total

namespace IsVar

  export
  coDeBruijn : {ctxt : _} ->
               DeBruijn.Variable.IsVar ctxt s ->
               Diamond (`CoDeBruijn.Variable.IsVar` s) ctxt
  coDeBruijn v@_ with (view v)
    coDeBruijn {ctxt = _ :< _} v@_ | Here = MkDiamond (Keep Refl none) Here
    coDeBruijn {ctxt = _ :< _} v@_ | There w = Skip (coDeBruijn w)

  export
  deBruijn : CoDeBruijn.Variable.IsVar g s ->
             DeBruijn.Variable.IsVar g s
  deBruijn Here = here


namespace Term

  export
  coDeBruijns : {ctxt, metas, tys : _} ->
                All (Term metas ctxt) tys ->
                Diamond (\ ctxt => CoTerms metas ctxt tys) ctxt

  export
  coDeBruijnS : {ctxt, metas, tys : _} ->
                Subst metas ctxt tys ->
                Diamond (\ ctxt => CoSubst metas ctxt tys) ctxt

  export
  coDeBruijnM : {ctxt, metas : _} ->
                (0 m : Meta) ->
                IsMember metas m ->
                Subst metas ctxt m.metaScope ->
                Diamond (\ ctxt => CoTerm metas ctxt m.metaType) ctxt
  coDeBruijnM (MkMeta nm nms ty) mem sg with (lookup mem)
    _ | (_ ** Refl) with (support nms)
      _ | (_ ** Refl)
        = Met mem <$> coDeBruijnS sg

  export
  coDeBruijn : {ctxt, metas, s : _} ->
               Term metas ctxt s ->
               Diamond (\ ctxt => CoTerm metas ctxt s) ctxt
  coDeBruijn (Var v) = Var <$> coDeBruijn v
  coDeBruijn (Met m sg) = coDeBruijnM _ m sg
  coDeBruijn (Fun b) = Fun <$> bind (coDeBruijn b)
  coDeBruijn (Call op ts) = Call op <$> coDeBruijns ts

  coDeBruijns [] = MkDiamond none []
  coDeBruijns (t :: ts) = Cons <$> relevant (coDeBruijn t) (coDeBruijns ts)

  coDeBruijnS [<] = MkDiamond none [<]
  coDeBruijnS (sg :< t) = Snoc <$> relevant (coDeBruijnS sg) (coDeBruijn t)

  export
  deBruijns : CoTerms metas ctxt tys ->
              Thinning ctxt ctxt' ->
              All (Term metas ctxt') tys

  export
  deBruijnS : CoSubst metas ctxt tys ->
              Thinning ctxt ctxt' ->
              Subst metas ctxt' tys

  export
  deBruijn : CoTerm metas ctxt s -> Thinning ctxt ctxt' -> Term metas ctxt' s
  deBruijn (Var v) th = Var (thin (deBruijn v) th)
  deBruijn (Met m sg) th = Met m (deBruijnS sg th)
  deBruijn (Fun (K b)) th = Fun (deBruijn b (Skip th))
  deBruijn (Fun (R x b)) th = Fun (deBruijn b (Keep Refl th))
  deBruijn (Call op ts) th = Call op (deBruijns ts th)

  deBruijns [] th = []
  deBruijns (Cons (MkRelevant {th = left} {ph = right} t _ ts)) th
    = deBruijn t (left <.> th) :: deBruijns ts (right <.> th)

  deBruijnS [<] th = [<]
  deBruijnS (Snoc (MkRelevant {th = left} {ph = right} sg _  t)) th
    = deBruijnS sg (left <.> th) :< deBruijn  t (right <.> th)
