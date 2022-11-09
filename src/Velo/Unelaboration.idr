module Velo.Unelaboration

import Data.List1
import Data.SnocList
import Data.SnocList.Quantifiers

import Velo.Types
import Velo.IR.Common
import Velo.IR.AST
import Velo.IR.Term

%default total

fresh : {0 ctxt : SnocList Ty} -> All Item ctxt -> Ty -> String
fresh nms ty
  = go (forget $ mapProperty (\ (I str _) => str) nms)
       ((,Nothing) <$> hints ty) where

  hints : Ty -> List1 String
  hints TyNat = "m" ::: ["n", "p", "q"]
  hints TyBool = "b" ::: ["x", "y"]
  hints (TyFunc x y) = "f" ::: ["g", "h"]

  toName : (String, Maybe Nat) -> String
  toName (str, mn) = maybe str ((str ++) . show) mn

  candidate : SnocList String -> List1 (String, Maybe Nat) -> Maybe String
  candidate used = choice . map (\ tn => delay $ do
    let nm = toName tn
    guard (not (nm `elem` used))
    pure nm)

  go : SnocList String -> List1 (String, Maybe Nat) -> String
  go used cs = case candidate used cs of
    Just str => str
    Nothing => assert_total (go used (map (map (Just . maybe 0 S)) cs))

var : All Item ctxt -> IsVar ctxt t -> String
var [<] v = absurd v
var (nms :< I x _) v@_ with (view v)
  _ | Here = x
  _ | There v' = var nms v'

meta : {0 m : Meta} -> {metas : _} ->
  All Item ctxt ->
  IsMember metas m ->
  Subst metas ctxt (metaScope m) ->
  RawEmpty

checking : {metas, t : _} -> All Item ctxt ->
           Term metas ctxt t -> RawEmpty
synthing : {metas, t : _} -> All Item ctxt ->
           Term metas ctxt t -> RawEmpty

meta nms p sg with (lookup p)
  _ | (MkMeta nm supp _ ** Refl) = go 0 supp sg (Branch (Hole nm) () Nil) where

    go : Nat -> All Item tys -> Subst metas ctxt tys -> RawEmpty -> RawEmpty
    go n [<] _ t = t
    go n (xs :< I x _) (sg :< u@(Var (V m p))) t
      = ifThenElse (n == m)
          (go (S n) xs sg t)
          (go (S n) xs sg (Branch (Let x) () [(synthing nms u), t]))
    go n (xs :< I x _) (sg :< u) t
      = go (S n) xs sg (Branch (Let x) () [(synthing nms u), t])

calling : {metas, tys : _} -> All Item ctxt ->
          Prim tys ty -> All (Term metas ctxt) tys -> RawEmpty
calling nms Zero ts
  = Branch Zero () Nil
calling nms Plus [t]
  = Branch Plus () [(checking nms t)]
calling nms Add [s,t]
  = Branch Add () [(checking nms s), (checking nms t)]
calling nms True ts
  = Branch T () Nil
calling nms False ts
  = Branch F () Nil
calling nms And [s,t]
  = Branch And () [(checking nms s), (checking nms t)]

calling nms App [f,t]
  = case f of
    Fun b => let x = fresh nms (typeOf t) in
             Branch (Let x) () [(synthing nms t), (synthing (nms :< I x _) b)]
    _ => Branch App () [(synthing nms f), (checking nms t)]

checking nms (Met m sg) = meta nms m sg
checking nms t = synthing nms t

synthing nms (Var v)
  = Branch (Ref (var nms v)) () Nil
synthing nms (Met m sg)
  = Branch (The t) () [meta nms m sg]
synthing nms (Fun {a = dom} b)
  = let x = fresh nms dom in
    Branch (Fun x dom) () [synthing (nms :< I x _) b]
synthing nms (Call op ts)
  = calling nms op ts

export
unelaborate : {metas, t : _} -> Term metas [<] t -> RawEmpty
unelaborate = synthing [<]
