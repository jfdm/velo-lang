module Velo.IR.Term

import Data.String
import Decidable.Equality

import Toolkit.Data.List.Pointwise
import public Toolkit.Data.List.Quantifiers
import Toolkit.Data.List.Subset
import Toolkit.Data.SnocList.Quantifiers
import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Variable

import Velo.Core
import Velo.Types
import Velo.IR.Common
import Velo.Elaborator.Common

import Velo.IR.Holey

import public Toolkit.DeBruijn.Renaming
import public Toolkit.DeBruijn.Substitution

%default total

------------------------------------------------------------------------
-- The type of meta variables

public export
record Meta where
  constructor MkMeta
  metaName : Name
  metaScope : List Ty
  metaScopeNames : All (\ _ => String) metaScope
  metaType : Ty

------------------------------------------------------------------------
-- The type of well-scoped terms with meta variables

public export
Thinning : (xs, ys : List a) -> Type
Thinning = Subset (===)

public export
data Term : (metas : List Meta) -> (ctxt : List Ty) -> Ty -> Type where
  Var : IsVar ctxt ty -> Term metas ctxt ty
  Met : IsVar metas m ->
        Thinning m.metaScope ctxt ->
        Term metas ctxt m.metaType
  Fun : Term metas (ctxt += a) b ->
        Term metas ctxt (TyFunc a b)
  Call : {tys : _} ->
         Prim tys ty ->
         All (Term metas ctxt) tys ->
         Term metas ctxt ty

------------------------------------------------------------------------
-- Renaming

public export
Rename Ty (Term []) where
  rename f (Var prf)
    = Var (f prf)

  rename f (Met v th)
    = void (absurd v)

  rename f (Fun body)
    = Fun (rename (weaken f) body)

  rename f (Call p ts)
    = Call p (assert_total $ map (rename f) ts)

  embed = Var

------------------------------------------------------------------------
-- Substitution

public export
Substitute Ty (Term []) where
  subst f (Var prf)
    = f prf

  subst f (Met v th)
    = void (absurd v)

  subst f (Fun body)
    = Fun (subst (weakens f) body)

  subst f (Call p ts)
    = Call p (assert_total $ map (subst f) ts)
