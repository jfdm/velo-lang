module Velo.Terms

import public Decidable.Equality

import public Toolkit.Data.List.Quantifiers

import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Variable
import public Toolkit.DeBruijn.Renaming
import public Toolkit.DeBruijn.Substitution

import Velo.Types
import Velo.IR.Common

%default total

public export
data Term : (ctxt : List Ty)
         -> (type : Ty)
         -> Type
  where
    Var : (prf : IsVar types type)
              -> Term  types type

    Fun : {a : Ty}
       -> (body : Term (types += a) b)
               -> Term types (TyFunc a b)

    Call : {tys : List Ty}
       -> (op : Prim tys ty)
       -> (args : All (Term ctxt) tys)
       -> Term ctxt ty

------------------------------------------------------------------------
-- Renaming

public export
Rename Ty Term where
  rename f (Var prf)
    = Var (f prf)

  rename f (Fun body)
    = Fun (rename (weaken f) body)

  rename f (Call p ts)
    = Call p (assert_total $ map (rename f) ts)

  embed = Var

------------------------------------------------------------------------
-- Substitution

public export
Substitute Ty Term where
  subst f (Var prf)
    = f prf

  subst f (Fun body)
    = Fun (subst (weakens f) body)

  subst f (Call p ts)
    = Call p (assert_total $ map (subst f) ts)

-- [ EOF ]
