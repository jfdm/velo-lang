module Velo.Pass.CSE

import Data.Nat
import Data.SortedMap

import Data.SnocList
import Data.SnocList.Quantifiers
import Decidable.Equality

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term
import Velo.IR.CoTerm
import Toolkit.DeBruijn.Variable
import Toolkit.CoDeBruijn
import Toolkit.Data.Comparison.Informative
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

record Candidate (metas : _) (ctxt : _) where
  constructor MkCandidate
  {cType : Ty}
  cTerm : Diamond (\ ctxt => CoTerm metas ctxt cType) ctxt

Eq (Candidate metas ctxt) where
  MkCandidate {cType = s} t == MkCandidate {cType = s'} t' with (decEq s s')
    MkCandidate {cType = s} t == MkCandidate {cType = .(s)} t'
      | Yes Refl = t == t'
    _ | No _ = False

Ord (Candidate metas ctxt) where
  compare (MkCandidate {cType = s} t) (MkCandidate {cType = s'} t') with (cmp s s')
    _ | LT = LT
    compare (MkCandidate {cType = s} t) (MkCandidate {cType = .(s)} t')
      | EQ = compare t t'
    _ | GT = GT

Candidates : (metas : List Meta) -> (ctxt : SnocList Ty) -> Type
Candidates metas ctxt = SortedMap (Candidate metas ctxt) Nat

thin : Candidates metas xs -> Thinning xs ys -> Candidates metas ys
thin cs th = fromList $ map adjust $ toList cs where

  adjust : (Candidate metas xs, Nat) -> (Candidate metas ys, Nat)
  adjust (MkCandidate t, n) = (MkCandidate (thin t th), n)

split : Candidates metas (ctxt :< s) ->
        (Candidates metas (ctxt :< s), Candidates metas ctxt)
split cs
  = let %hint natPlus : Semigroup Nat; natPlus = MkSemigroup (+) in
    flip foldMap (SortedMap.toList cs) $ uncurry $ \ (MkCandidate tm), n =>
    case thick tm of
      Nothing => (singleton (MkCandidate tm) n, empty)
      Just tm => (empty, singleton (MkCandidate tm) n)

cse : {metas, ctxt, t : _} ->
      Diamond (\ ctxt => CoTerm metas ctxt t) ctxt ->
      Diamond (\ ctxt => CoTerm metas ctxt t) ctxt
cse (MkDiamond th t) = MkDiamond th (snd $ go t) where

  go : {metas, ctxt, t : _} ->
    CoTerm metas ctxt t ->
    (Candidates metas ctxt, CoTerm metas ctxt t)

  gos : {metas, ctxt, ts : _} ->
    CoTerms metas ctxt ts ->
    (Candidates metas ctxt, CoTerms metas ctxt ts)

  goB : {metas, ctxt, x, t : _} ->
    Binding (\ ctxt => CoTerm metas ctxt t) x ctxt ->
    (Candidates metas ctxt, Binding (\ ctxt => CoTerm metas ctxt t) x ctxt)

  go (Fun b) =
    let (cs, b) = goB b in
    let tm = Fun b in
    (insert (MkCandidate (MkDiamond Identity tm)) 1 cs, tm)
  go (Call op ts) =
    let (cs, ts) = gos ts in
    let tm = Call op ts in
    (insert (MkCandidate (MkDiamond Identity tm)) 1 cs, tm)
  go t = (empty, t)

  gos [] = (empty, [])
  gos (Cons (MkRelevant {th = left, ph = right} t cover ts)) =
    let (cs1, t) = go t in
    let (cs2, ts) = gos ts in
    ( mergeWith (+) (thin cs1 left) (thin cs2 right)
    , Cons (MkRelevant t cover ts))

  goB (K b) = map K (go b)
  goB (R x b) =
    let (cs, b) = go b in
    let (locals, cs) = split cs in
    (cs, R x ?hg_1)
