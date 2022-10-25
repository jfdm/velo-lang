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

meta : {metas : List Meta} -> IsMember metas m -> AST ()
meta m = Hole () (metaName $ fst $ lookup m)

checking : {metas, t : _} -> All Item ctxt ->
           Term metas ctxt t -> AST ()
synthing : {metas, t : _} -> All Item ctxt ->
           Term metas ctxt t -> AST ()

calling : {metas, tys : _} -> All Item ctxt ->
          Prim tys ty -> All (Term metas ctxt) tys -> AST ()
calling nms Zero ts = Zero ()
calling nms Plus [t] = Plus () (checking nms t)
calling nms Add [s,t] = Add () (checking nms s) (checking nms t)
calling nms True ts = T ()
calling nms False ts = F ()
calling nms And [s,t] = And () (checking nms s) (checking nms t)
calling nms App [f,t] = case f of
  Fun b => let x = fresh nms (typeOf t) in
           Let () x (synthing nms t) (synthing (nms :< I x _) b)
  _ => App () (synthing nms f) (checking nms t)

checking nms (Met m sg) = meta m -- TODO: unelab the substitution
checking nms t = synthing nms t

synthing nms (Var v) = Ref () (var nms v)
synthing nms (Met m sg) = The () t (meta m) -- TODO: unelab the substitution
synthing nms (Fun {a = dom} b)
  = let x = fresh nms dom in
    Fun () x dom (synthing (nms :< I x _) b)
synthing nms (Call op ts) = calling nms op ts

export
unelaborate : {metas, t : _} -> Term metas [<] t -> AST ()
unelaborate = synthing [<]
