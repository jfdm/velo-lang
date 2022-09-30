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

------------------------------------------------------------------------
-- Decidable equality for primitives

namespace Prim

------------------------------------------------------------------------
-- Decidable equality

export Injective Var where injective Refl = Refl
export Biinjective Call where biinjective Refl = (Refl, Refl)

export {0 x : a} -> {0 xs : List a} -> {0 p : a -> Type} ->
  Biinjective (All.(::) {p, x, xs}) where biinjective Refl = (Refl, Refl)

namespace Term

  public export
  data HeadSim : (t, u : Term ctxt ty) -> Type where
    Var  : (v, w : _) -> HeadSim (Var v) (Var w)
    Fun  : (t, u : _) -> HeadSim (Fun t) (Fun u)
    Call : (tys, uys : List Ty) ->
           (p : Prim tys ty) -> (ts : All (Term ctxt) tys) ->
           (q : Prim uys ty) -> (us : All (Term ctxt) uys) ->
           HeadSim (Call p ts) (Call q us)

  public export
  headSim : (t, u : Term ctxt ty) -> Maybe (HeadSim t u)
  headSim (Var _) (Var _) = pure (Var _ _)
  headSim (Fun _) (Fun _) = pure (Fun _ _)
  headSim (Call _ _) (Call _ _) = pure (Call _ _ _ _ _ _)
  headSim _ _ = Nothing

  export
  headSimFullDiag : (t : Term ctxt ty) -> Not (headSim t t === Nothing)
  headSimFullDiag (Var _) = absurd
  headSimFullDiag (Fun _) = absurd
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
