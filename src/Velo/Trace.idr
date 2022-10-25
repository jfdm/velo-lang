module Velo.Trace

import Data.SnocList.Quantifiers
import Data.String
import public Text.PrettyPrint.Prettyprinter

import Toolkit.Item
import Toolkit.DeBruijn.Context
import Toolkit.Data.Location

import Velo.Types
import Velo.IR.AST
import Velo.IR.Term
import Velo.IR.Common
import Velo.Values
import Velo.Unelaboration

import Velo.Semantics.Reductions

import Velo.Eval

import Velo.Core

%default total

namespace Velo
  namespace Types
    ty : Prec -> Ty -> Doc ann
    ty _ (TyNat) = pretty "Nat"
    ty _ (TyBool) = pretty "Bool"
    ty d (TyFunc x y)
      = parenthesise (d > Open) $
         hsep [ty App x, pretty "->", ty Open y]


    export
    Pretty Ty where
      prettyPrec = ty

var : IsVar ctxt type -> Doc ann
var (V pos prf) = pretty pos

namespace Velo
  namespace Core
    velo : {metas : _} -> Prec -> Term metas ctxt type -> Doc ann
    velos : {metas : _} -> All Item tys -> Subst metas ctxt tys -> SnocList (Doc ann)

    meta : {metas : _} ->
           (ms : List Meta) -> (n : Nat) -> (0 _ : AtIndex m ms n) ->
           Subst metas ctxt m.metaScope ->
           Doc ann
    meta (MkMeta nm {metaScope} nms ty  :: _) 0 Here sg
      = let hole = "?" <+> pretty nm in
        case velos nms sg of
          [<] => hole
          asss => hole <++> encloseSep "{" "}" ", " (asss <>> [])
    meta (_ :: metas) (S n) (There p) sg = meta metas n p sg

    velos nms sg = gos 0 nms sg where

      go : Bool -> Nat ->  String -> Term metas ctxt s -> List (Doc ann)
      go b n x t =
        let doc = delay (pretty x <++> "=" <++> velo Open t) in
        case t of
          Var (V m _) => ifThenElse (m == n) [] [doc]
          _ => [doc]

      gos : Nat -> forall tys. All Item tys -> Subst metas ctxt tys -> SnocList (Doc ann)
      gos n [<] [<] = [<]
      gos n [<I x _] [<t] = [<] <>< go False n x t
      gos n (nms :< I x _) (sg :< t) = gos (S n) nms sg <>< go True n x t

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

    export
    {metas : _} -> Pretty (Term metas ctxt type) where
      prettyPrec = velo

  namespace AST

    ast : AST a -> Doc ann
    ast (Ref _ n)
      = pretty n

    ast (Hole _ n)
      = pretty ("?" <+> n) -- must be seen as one.

    ast (Zero _)
      = pretty "zero"

    ast (Plus _ tm)
      = group
      $ parens
      $ hsep [ pretty "inc"
             , ast tm
             ]

    ast (Add _ l r)
      = group
      $ parens
      $ hsep [ pretty "add"
             , ast l
             , ast r
             ]

    ast (T _)
      = pretty "true"

    ast (F _)
      = pretty "false"

    ast (And _ l r)
      = group
      $ parens
      $ hsep [ pretty "and"
             , ast l
             , ast r
             ]

    ast (Let _ n value body)
      = vsep [ group
             $ hsep [ pretty "let"
                    , pretty n
                    , equals
                    , ast value]
             , hang 3
             $ hsep [ pretty "in"
                    , ast body
                    ]
             ]

    ast (Fun _ n type body)
      = group
      $ parens
      $ vsep [ hsep [ pretty "fun"
                    , pretty n
                    , colon
                    , pretty type
                    ]
             , hang 3
             $ hsep [ pretty "=>"
                    , ast body
                    ]
             ]

    ast (App _ f a)
      = parens
      $ group
      $ align
      $ vsep [ ast f
             , ast a
             ]

    ast (The _ type tm)
      = group
      $ parens
      $ align
      $ hsep [ ast tm
             , colon
             , pretty type
             ]

    export
    Pretty (AST a) where
      pretty = ast

prettyRedux : Redux a b -> Doc ()
prettyRedux (SimplifyCall And (x !: _))
  = pretty "Simplify And Left Operand by"
    <++>
    prettyRedux x

prettyRedux (SimplifyCall And (x :: y !: _))
  = pretty "Simplify And Right Operand by"
    <++>
    prettyRedux y

prettyRedux (ReduceAndTT)
  = pretty "Reduce And True True"
prettyRedux (ReduceAndWF)
  = pretty "Reduce And Right is False"
prettyRedux (ReduceAndFW)
  = pretty "Reduce And Left is False"

prettyRedux (SimplifyCall Add (x !: _))
  = pretty "Simplify Add Left Operand by"
    <++>
    prettyRedux x

prettyRedux (SimplifyCall Add (x :: y !: _))
  = pretty "Simplify Add Right Operand by"
    <++>
    prettyRedux y

prettyRedux (ReduceAddZW vr)
  = pretty "Reduce Add Left is Zero"

prettyRedux (RewriteEqNatPW vl vr)
  = pretty "Rewriting Add"

prettyRedux (SimplifyCall Plus (x !: _))
  = pretty "Simplify Plus by"
    <++>
    prettyRedux x

prettyRedux (SimplifyCall App (_ !: _))
  = pretty "Simplify Application Function"

prettyRedux (SimplifyCall App (_ :: var !: _))
  = pretty "Simplify Application Variable by"
    <++>
    prettyRedux var
prettyRedux (ReduceFuncApp x)
  = pretty "Reduce Application"


wrap : {metas, type : _} -> Term metas [<] type -> Doc ()
wrap {type} tm
  = vcat [ pretty "```"
         , pretty (unelaborate tm)
         , pretty "```"
         ]


showSteps : {metas, ty : _}
         -> {a,b : Term metas [<] ty}
         -> Reduces Redux a b
         -> List (Doc ())
showSteps {a = a} {b = a} Nil
  = [wrap a]

showSteps {a = a} {b = b} (x :: y)
  = wrap a :: (hsep [pretty "###", prettyRedux x]) :: showSteps y

export
prettyComputation : {metas, ty : _}
                 -> {term : Term metas [<] ty}
                 -> (res  : Result Value Redux term)
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
  = printLn
  $ annotate ()
  $ vcat (pretty <$> metas)

-- [ EOF ]
