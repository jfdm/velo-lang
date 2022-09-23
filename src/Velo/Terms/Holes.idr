module Velo.Terms.Holes

import public Decidable.Equality

import public Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Variable
import public Toolkit.DeBruijn.Renaming
import public Toolkit.DeBruijn.Substitution

import Velo.Types

public export
data Term : (i,o  : List (Ty,List Ty))
         -> (ctxt : List Ty)
         -> (type : Ty)
         -> Type
  where
    Hole : Term h ((ty,ctxt)::h) ctxt ty

    Var : (prf : IsVar     types type)
              -> Term  h h types type

    Fun : {a,b : Ty}
       -> (body : Term i o (types += a) b)
               -> Term i o types (TyFunc a b)

    Let : {a,b : Ty}
       -> (val : Term x y ctxt a)
       -> (scope : Term y z (ctxt += a) b)
                -> Term x z  ctxt b

    App : {a,b : Ty}
       -> (func : Term x y ctxt (TyFunc a b))
       -> (arg  : Term y z ctxt         a)
               -> Term x z ctxt           b

    Zero : Term h h types TyNat

    Plus : Term x y types TyNat
        -> Term x y types TyNat

    Add : (l : Term a b types TyNat)
       -> (r : Term b c types TyNat)
            -> Term a c types TyNat

    True,False : Term h h types TyBool

    And : (l : Term a b types TyBool)
       -> (r : Term b c types TyBool)
            -> Term a c types TyBool


-- [ EOF ]
