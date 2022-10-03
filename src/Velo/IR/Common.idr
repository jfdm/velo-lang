module Velo.IR.Common

import Decidable.Equality

import Velo.Types

%default total

public export
Name : Type
Name = String

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

    App   : Prim [TyFunc dom cod, dom] cod

namespace Prim

  public export
  data HeadSim : (p : Prim tys1 ty1) -> (q : Prim tys2 ty2) -> Type where
    Zero  : HeadSim Zero Zero
    Plus  : HeadSim Plus Plus
    Add   : HeadSim Add Add
    True  : HeadSim True True
    False : HeadSim False False
    And   : HeadSim And And
    App   : HeadSim App App

  public export
  headSim : (p : Prim tys1 ty1) -> (q : Prim tys2 ty2) -> Maybe (HeadSim p q)
  headSim Zero Zero = Just Zero
  headSim Plus Plus = Just Plus
  headSim Add Add = Just Add
  headSim True True = Just True
  headSim False False = Just False
  headSim And And = Just And
  headSim App App = Just App
  headSim _ _ = Nothing

  export
  headSimFullDiag : (p : Prim tys ty) -> Not (headSim p p === Nothing)
  headSimFullDiag Zero = absurd
  headSimFullDiag Plus = absurd
  headSimFullDiag Add = absurd
  headSimFullDiag True = absurd
  headSimFullDiag False = absurd
  headSimFullDiag And = absurd
  headSimFullDiag App = absurd

  export
  hetDecEq : {tys1, tys2 : List Ty} ->
             (p : Prim tys1 ty1) -> (q : Prim tys2 ty2) ->
             Dec (tys1 === tys2, ty1 === ty2, p ~=~ q)
  hetDecEq p@_ q@_ with (headSim p q) proof hdSim
      _ | Just Zero = Yes (Refl, Refl, Refl)
      _ | Just Plus = Yes (Refl, Refl, Refl)
      _ | Just Add = Yes (Refl, Refl, Refl)
      _ | Just True = Yes (Refl, Refl, Refl)
      _ | Just False = Yes (Refl, Refl, Refl)
      _ | Just And = Yes (Refl, Refl, Refl)
      hetDecEq
        {tys1 = [TyFunc dom1 cod1, _]}
        {tys2 = [TyFunc dom2 cod2, _]}
        p@_ q@_ | Just App with (decEq dom1 dom2, decEq cod1 cod2)
          _ | (Yes eq1, Yes eq2) = Yes (rewrite eq1 in rewrite eq2 in (Refl, Refl, Refl))
          _ | (No neq1, _) = No (\case (Refl, _, _) => neq1 Refl)
          _ | (_, No neq2) = No (\case (Refl, _, _) => neq2 Refl)
      _ | Nothing = No (\ (Refl, Refl, Refl) => headSimFullDiag _ hdSim)

  export
  {tys : List Ty} -> DecEq (Prim tys ty) where
    decEq p q = case hetDecEq p q of
      Yes (_, _, eq) => Yes eq
      No neq => No (\ eq => neq (Refl, Refl, eq))
