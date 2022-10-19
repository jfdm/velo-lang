module Velo.Pass.CSE

import Data.SnocList
import Data.SnocList.Quantifiers
import Decidable.Equality

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term
import Velo.IR.CoTerm
import Toolkit.DeBruijn.Variable
import Toolkit.CoDeBruijn
import Toolkit.Data.SnocList.Thinning

import Velo.Elaborator.CoDeBruijn

%default total

||| abstract here (provided things match up)
abstractH : {metas, g, g', ctx, s, t : _} ->
            DeBruijn.Variable.IsVar (g <+> g') s ->
            Diamond (\ ctxt => CoTerm metas ctxt s) g ->
            Diamond (\ ctxt => CoTerm metas ctxt t) (g <+> ctx) ->
            Maybe (Diamond (\ ctxt => CoTerm metas ctxt t) ((g <+> g') <+> ctx))
abstractH v se@(MkDiamond {support = xs@_} th se'@_) tm@(MkDiamond {support = ys} ph tm')
  with (decEq s t)
  _ | No p = Nothing
  _ | Yes Refl with (eqTh (th <+> none) ph)
    _ | No p = Nothing
    _ | Yes (Refl, _) with (decEq se' tm')
      _ | Yes Refl = pure (coDeBruijn (Var (shifts v)))
      _ | No p = Nothing

first : {xs : SnocList a} ->
        ({x : a} -> DeBruijn.Variable.IsVar (ys <+> xs) x -> p x -> Maybe b) ->
        All p xs -> Maybe b
first p [<] = Nothing
first p (xs :< x) = p here x <|> first (p . shift) xs

export
abstractR : {metas, g, g', ctx, t : _} ->
            All (\ s => Diamond (\ ctxt => CoTerm metas ctxt s) g) g' ->
            Diamond (\ ctxt => CoTerm metas ctxt t) (g <+> ctx) ->
            Diamond (\ ctxt => CoTerm metas ctxt t) ((g <+> g') <+> ctx)

abstractRs : {metas, g, g', ctx, tys : _} ->
             All (\ s => Diamond (\ ctxt => CoTerm metas ctxt s) g) g' ->
             Diamond (\ ctxt => CoTerms metas ctxt tys) (g <+> ctx) ->
             Diamond (\ ctxt => CoTerms metas ctxt tys) ((g <+> g') <+> ctx)

abstractR ses tm = case first (\ v, se => abstractH v se tm) ses of
  Just tm => tm
  Nothing => case tm of
    (MkDiamond th (Fun (K b))) =>
      (Fun . K) <$> abstractR ses (MkDiamond th b)
    (MkDiamond th (Fun (R x b))) =>
      Fun <$> bind (abstractR {ctx = ctx :< x} ses (MkDiamond (Keep Refl th) b))
    (MkDiamond th (Call op ts)) =>
      Call op <$> abstractRs ses (MkDiamond th ts)
    _ => thin tm (Skips ones {zs = g'} <+> ones)

abstractRs ses (MkDiamond th []) = MkDiamond none []
abstractRs ses (MkDiamond th (Cons (MkRelevant {th = left, ph = right} t _ ts)))
  = let t = assert_total $ abstractR ses (MkDiamond (left <.> th) t) in
    let ts = assert_total $ abstractRs ses (MkDiamond (right <.> th) ts) in
    Cons <$> relevant t ts
