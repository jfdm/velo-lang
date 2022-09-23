module Velo.Terms

import public Decidable.Equality

import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Variable
import public Toolkit.DeBruijn.Renaming
import public Toolkit.DeBruijn.Substitution

import Velo.Types

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

    App : {a : Ty}
       -> (func : Term ctxt (TyFunc a b))
       -> (arg  : Term ctxt         a)
               -> Term ctxt           b

    Zero : Term types TyNat
    Plus : Term types TyNat -> Term types TyNat

    Add : (l,r : Term types TyNat) -> Term types TyNat

    True,False : Term types TyBool

    And : (l,r : Term types TyBool) -> Term types TyBool

public export
Rename Ty Term where
  rename f (Var prf)
    = Var (f prf)

  rename f (Fun body)
    = Fun (rename (weaken f) body)

  rename f (App f' a)
    = App (rename f f')
          (rename f a)

  rename f Zero
    = Zero

  rename f (Plus x)
    = Plus (rename f x)


  rename f (Add l r)
    = Add (rename f l)
          (rename f r)

  rename f True
    = True

  rename f False
    = False

  rename f (And l r)
    = And (rename f l)
          (rename f r)

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

  subst f Zero
    = Zero

  subst f (Plus x)
    = Plus (subst f x)

  subst f (Add l r)
    = Add (subst f l)
          (subst f r)


  subst f True
    = True

  subst f False
    = False

  subst f (And l r)
    = And (subst f l)
          (subst f r)

-- [ EOF ]
