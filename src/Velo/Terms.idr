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

------------------------------------------------------------------------
-- Renaming

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

------------------------------------------------------------------------
-- Substitution

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

------------------------------------------------------------------------
-- Decidable equality for primitives

namespace Prim

  public export
  data HeadSim : (p, q : Prim tys ty) -> Type where
    Zero  : HeadSim Zero Zero
    Plus  : HeadSim Plus Plus
    Add   : HeadSim Add Add
    True  : HeadSim True True
    False : HeadSim False False
    And   : HeadSim And And

  public export
  headSim : (p, q : Prim tys ty) -> Maybe (HeadSim p q)
  headSim Zero Zero = Just Zero
  headSim Plus Plus = Just Plus
  headSim Add Add = Just Add
  headSim True True = Just True
  headSim False False = Just False
  headSim And And = Just And
  headSim _ _ = Nothing

  export
  headSimFullDiag : (p : Prim tys ty) -> Not (headSim p p === Nothing)
  headSimFullDiag Zero = absurd
  headSimFullDiag Plus = absurd
  headSimFullDiag Add = absurd
  headSimFullDiag True = absurd
  headSimFullDiag False = absurd
  headSimFullDiag And = absurd

  export
  DecEq (Prim tys ty) where
    decEq p@_ q@_ with (headSim p q) proof hdSim
      _ | Just Zero = Yes Refl
      _ | Just Plus = Yes Refl
      _ | Just Add = Yes Refl
      _ | Just True = Yes Refl
      _ | Just False = Yes Refl
      _ | Just And = Yes Refl
      _ | Nothing = No (\ Refl => headSimFullDiag _ hdSim)

------------------------------------------------------------------------
-- Decidable equality

export Injective Var where injective Refl = Refl
export Biinjective App where biinjective Refl = (Refl, Refl)
export Biinjective Call where biinjective Refl = (Refl, Refl)

export {0 x : a} -> {0 xs : List a} -> {0 p : a -> Type} ->
  Biinjective (All.(::) {p, x, xs}) where biinjective Refl = (Refl, Refl)

namespace Term

  public export
  data HeadSim : (t, u : Term ctxt ty) -> Type where
    Var  : (v, w : _) -> HeadSim (Var v) (Var w)
    Fun  : (t, u : _) -> HeadSim (Fun t) (Fun u)
    App  : (a, b : _) ->
           (f : Term ctxt (TyFunc a ty)) -> (t : _) ->
           (g : Term ctxt (TyFunc b ty)) -> (u : _) ->
           HeadSim (App f t) (App g u)
    Call : (tys, uys : List Ty) ->
           (p : Prim tys ty) -> (ts : All (Term ctxt) tys) ->
           (q : Prim uys ty) -> (us : All (Term ctxt) uys) ->
           HeadSim (Call p ts) (Call q us)

  public export
  headSim : (t, u : Term ctxt ty) -> Maybe (HeadSim t u)
  headSim (Var _) (Var _) = pure (Var _ _)
  headSim (Fun _) (Fun _) = pure (Fun _ _)
  headSim (App _ _) (App _ _) = pure (App _ _ _ _ _ _)
  headSim (Call _ _) (Call _ _) = pure (Call _ _ _ _ _ _)
  headSim _ _ = Nothing

  export
  headSimFullDiag : (t : Term ctxt ty) -> Not (headSim t t === Nothing)
  headSimFullDiag (Var _) = absurd
  headSimFullDiag (Fun _) = absurd
  headSimFullDiag (App _ _) = absurd
  headSimFullDiag (Call _ _) = absurd

  public export
  decEqTerm : (t, u : Term ctxt ty) -> Dec (t === u)
  public export
  decEqTerms : (ts, us : All (Term ctxt) tys) -> Dec (ts === us)
  public export
  decEqHeadSim : {0 t, u : Term ctxt ty} -> HeadSim t u -> Dec (t === u)

  decEqHeadSim (Var v w) = decEqCong (decEq v w)
  decEqHeadSim (Fun t u) with (decEqTerm t u)
    _ | Yes eq = Yes (cong Fun eq)
    _ | No neq = No (\case Refl => neq Refl)
  decEqHeadSim (App a b f t g u) with (decEq a b)
    decEqHeadSim (App a .(a) f t g u) | Yes Refl
      = decEqCong2 (decEqTerm f g) (decEqTerm t u)
    _ | No neq = No (\case Refl => neq Refl)
  decEqHeadSim (Call tys uys p ts q us) with (decEq tys uys)
    decEqHeadSim (Call tys .(tys) p ts q us) | Yes Refl
      = decEqCong2 (decEq p q) (decEqTerms ts us)
    _ | No neq = No (\case Refl => neq Refl)

  decEqTerm t u with (headSim t u) proof hdSim
    decEqTerm t u | Nothing = No (\ Refl => headSimFullDiag _ hdSim)
    decEqTerm t u | Just prf = decEqHeadSim prf

  decEqTerms [] [] = Yes Refl
  decEqTerms (t :: ts) (u :: us) = decEqCong2 (decEqTerm t u) (decEqTerms ts us)

public export
DecEq (Term ctxt ty) where
  decEq = decEqTerm

-- [ EOF ]
