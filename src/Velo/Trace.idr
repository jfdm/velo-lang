module Velo.Trace

import Data.String
import Text.PrettyPrint.Prettyprinter

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.Data.Location
import Velo.Types
import Velo.IR.Term
import Velo.IR.Common
import Velo.Values

import Velo.Elaborator

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

meta : (metas : List Meta) -> (n : Nat) -> (0 _ : AtIndex _ metas n) -> Doc ann
meta (m :: _) 0 p = "?" <+> pretty m.metaName
meta (_ :: metas) (S n) (There p) = meta metas n p

velo : {metas : _} -> Prec -> Term metas ctxt type -> Doc ann
velo d (Var prf)
  = var prf

velo d (Met (V n p) th)
  = meta metas n p

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


wrap : {type : Ty} -> Term [] [] type -> Doc ()
wrap {type} tm
  = vcat [ pretty "```"
         , pretty tm
         , pretty "```"
         ]


showSteps : {ty : Ty} -> {a,b : Term [] [] ty} -> Reduces a b -> List (Doc ())
showSteps {a = a} {b = a} Refl
  = [wrap a]

showSteps {a = a} {b = b} (Trans x y)
  = wrap a :: (pretty $ "### " <+> showRedux x) :: showSteps y

export
prettyComputation : {ty : Ty}
                 -> {term : Term [] [] ty}
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

hole : Hole h -> Doc ()
hole (H fc str t c)
  = vcat [hcat [pretty (show fc), pretty str]
         , vcat (ctxt c ++ [pretty "---", pretty (I str t)])
         ]


holes' : Holes holes -> List (Doc ())
holes' [] = []
holes' (elem :: rest)
  = (vcat [hole elem, pretty ""]) :: holes' rest

export
prettyHoles : Holes ss -> Velo ()
prettyHoles h
  = printLn $ vcat (holes' h)

export
Pretty Meta where
  pretty (MkMeta nm [] [] ty) = pretty (I ("?" ++ nm) ty)
  pretty (MkMeta nm ctxt nms ty)
    = vcat (displayAssumptions ctxt nms [<]
            <>> [pretty (String.replicate 10 '-'), pretty (I ("?" ++ nm) ty), ""])

    where

    displayAssumptions :
      (ctxt : List Ty) ->
      All (\ _ => String) ctxt ->
      SnocList (Doc ann) ->
      SnocList (Doc ann)
    displayAssumptions [] [] acc = acc
    displayAssumptions (ty :: tys) (nm :: nms) acc
      = displayAssumptions tys nms (acc :< pretty (I nm ty))

export
prettyMetas : List Meta -> Velo ()
prettyMetas metas
  = printLn $ vcat {ann = ()} (pretty <$> metas)

-- [ EOF ]
