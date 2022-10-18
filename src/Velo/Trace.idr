module Velo.Trace

import Data.SnocList.Quantifiers
import Data.String
import public Text.PrettyPrint.Prettyprinter

import Toolkit.Item
import Toolkit.DeBruijn.Context
import Toolkit.Data.Location
import Velo.Types
import Velo.IR.Term
import Velo.IR.Common
import Velo.Values

import Velo.Semantics.Reductions
import Velo.Semantics.Evaluation

import Velo.Core

%default total

ty : Prec -> Ty -> Doc ann
ty _ (TyNat) = pretty "Nat"
ty _ (TyBool) = pretty "Bool"
ty d (TyFunc x y)
  = parenthesise (d > Open) $
     hsep [ty App x, pretty "->", ty Open y]

var : IsVar ctxt type -> Doc ann
var (V pos prf) = pretty pos

velo : {metas : _} -> Prec -> Term metas ctxt type -> Doc ann
velos : {metas : _} -> All Item tys -> Subst metas ctxt tys -> Doc ann

meta : {metas : _} ->
       (ms : List Meta) -> (n : Nat) -> (0 _ : AtIndex m ms n) ->
       Subst metas ctxt m.metaScope ->
       Doc ann
meta (MkMeta nm {metaScope} nms ty  :: _) 0 Here sg
  = let hole = "?" <+> pretty nm in
    case nms of
      [<] => hole
      _ => hole <++> velos nms sg
meta (_ :: metas) (S n) (There p) sg = meta metas n p sg

velos nms sg = "{" <+> go nms sg <+> "}" where

  go : forall tys. All Item tys -> Subst metas ctxt tys -> Doc ann
  go [<] [<] = ""
  go [<I x _] [<t] = pretty x <++> "=" <++> velo Open t
  go (nms :< I x _) (sg :< t)
    = go nms sg <+> "," <++> pretty x <++> "=" <++> velo Open t

velo d (Var prf)
  = var prf

velo d (Met (V n p) sg)
  = meta metas n p sg

velo d (Fun body)

  = parenthesise (d > Open) (pretty "fun" <++> velo Open body)

velo d (Call App [f, a])
  = parenthesise (d >= App) (pretty "apply" <++> align (vsep [velo Dollar f, velo App a]))

velo _ (Call Zero []) = pretty "zero"
velo d (Call Plus [x])
  = group $ parenthesise (d > Open) $
      hsep [pretty "inc", velo App x]
velo d (Call Add [l, r])
  = group $ parenthesise (d > Open) $
      hsep [pretty "add", velo App l, velo App r]
velo _ (Call True []) = pretty "True"
velo _ (Call False []) = pretty "False"
velo d (Call And [l, r])
  = group $ parenthesise (d > Open) $
      hsep [pretty "and", velo App l, velo App r]

namespace Velo

  export
  {metas : _} -> Pretty (Term metas ctxt type) where
    prettyPrec = velo

  export
  Pretty Ty where
    prettyPrec = ty


showRedux : Redux a b -> String
showRedux (SimplifyCall And (x !: _)) = "Simplify And Left Operand by " ++ showRedux x
showRedux (SimplifyCall And (x :: y !: _)) = "Simplify And Right Operand by " ++ showRedux y
showRedux (ReduceAndTT) = "Reduce And True True"
showRedux (ReduceAndWF) = "Reduce And Right is False"
showRedux (ReduceAndFW) = "Reduce And Left is False"

showRedux (SimplifyCall Add (x !: _)) = "Simplify Add Left Operand by " ++ showRedux x
showRedux (SimplifyCall Add (x :: y !: _)) = "Simplify Add Right Operand by " ++ showRedux y
showRedux (ReduceAddZW vr) = "Reduce Add Left is Zero"
showRedux (RewriteEqNatPW vl vr) = "Rewriting Add"

showRedux (SimplifyCall Plus (x !: _)) = "Simplify Plus by " ++ showRedux x

showRedux (SimplifyCall App (_ !: _)) = "Simplify Application Function"
showRedux (SimplifyCall App (_ :: var !: _)) = "Simplify Application Variable by " ++ showRedux var
showRedux (ReduceFuncApp x) = "Reduce Application"


wrap : {metas, type : _} -> Term metas [<] type -> Doc ()
wrap {type} tm
  = vcat [ pretty "```"
         , pretty tm
         , pretty "```"
         ]


showSteps : {metas, ty : _} -> {a,b : Term metas [<] ty} -> Reduces a b -> List (Doc ())
showSteps {a = a} {b = a} Refl
  = [wrap a]

showSteps {a = a} {b = b} (Trans x y)
  = wrap a :: (pretty $ "### " <+> showRedux x) :: showSteps y

export
prettyComputation : {metas, ty : _}
                 -> {term : Term metas [<] ty}
                 -> (res  : Result term)
                         -> Velo ()
prettyComputation {term = term} (R that val steps)
  = printLn $ vcat (showSteps steps)

export
Pretty kind => Pretty (Item {kind} a) where
  pretty (I str a)
    = hsep [ pretty str
           , pretty ":"
           , pretty a]

ctxt : Context Ty is -> List (Doc ())
ctxt [] = []
ctxt (elem :: rest)
  = pretty elem :: ctxt rest

export
Pretty Meta where
  pretty (MkMeta nm [<] ty) = pretty (I ("?" ++ nm) ty)
  pretty (MkMeta nm nms ty)
    = vcat (displayAssumptions [] nms
            <>> [pretty (String.replicate 10 '-'), pretty (I ("?" ++ nm) ty), ""])

    where

    displayAssumptions :
      (seen : List String) ->
      {0 scp : SnocList Ty} ->
      All Item scp ->
      SnocList (Doc ann)
    displayAssumptions seen [<] = [<]
    displayAssumptions seen (is :< I str x)
      = ifThenElse (str `elem` seen)
          (displayAssumptions seen is)
          (displayAssumptions (str :: seen) is :< pretty (I str x))

export
prettyMetas : List Meta -> Velo ()
prettyMetas metas
  = printLn $ vcat {ann = ()} (pretty <$> metas)

-- [ EOF ]
