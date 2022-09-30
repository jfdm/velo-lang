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
  data HeadSim : (p, q : Prim tys ty) -> Type where
    Zero  : HeadSim Zero Zero
    Plus  : HeadSim Plus Plus
    Add   : HeadSim Add Add
    True  : HeadSim True True
    False : HeadSim False False
    And   : HeadSim And And
    App   : HeadSim App App

  public export
  headSim : (p, q : Prim tys ty) -> Maybe (HeadSim p q)
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
  DecEq (Prim tys ty) where
    decEq p@_ q@_ with (headSim p q) proof hdSim
      _ | Just Zero = Yes Refl
      _ | Just Plus = Yes Refl
      _ | Just Add = Yes Refl
      _ | Just True = Yes Refl
      _ | Just False = Yes Refl
      _ | Just And = Yes Refl
      _ | Just App = Yes Refl
      _ | Nothing = No (\ Refl => headSimFullDiag _ hdSim)
