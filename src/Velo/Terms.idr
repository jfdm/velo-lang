module Velo.Terms

import public Decidable.Equality

import public Toolkit.Data.List.Quantifiers

import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Variable
import public Toolkit.DeBruijn.Renaming
import public Toolkit.DeBruijn.Substitution

import Velo.Types

%default total

public export
data Prim : (args : List Ty)
         -> (type : Ty)
         -> Type
  where
    Zero  : Prim [] TyNat
    Plus  : Prim [TyNat] TyNat
    Add   : Prim [TyNat, TyNat] TyNat
    True  : Prim [] TyBool
    False : Prim [] TyBool
    And   : Prim [TyBool, TyBool] TyBool

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

    App : {a : Ty}
       -> (func : Term ctxt (TyFunc a b))
       -> (arg  : Term ctxt         a)
               -> Term ctxt           b

    Call : {tys : List Ty}
       -> (op : Prim tys ty)
       -> (args : All (Term ctxt) tys)
       -> Term ctxt ty

public export
Rename Ty Term where
  rename f (Var prf)
    = Var (f prf)

  rename f (Fun body)
    = Fun (rename (weaken f) body)

  rename f (App f' a)
    = App (rename f f')
          (rename f a)

  rename f (Call p ts)
    = Call p (assert_total $ map (rename f) ts)

  embed = Var

public export
Substitute Ty Term where
  subst f (Var prf)
    = f prf

  subst f (Fun body)
    = Fun (subst (weakens f) body)

  subst f (App f' a)
    = App (subst f f')
          (subst f a)

  subst f (Call p ts)
    = Call p (assert_total $ map (subst f) ts)

-- [ EOF ]
