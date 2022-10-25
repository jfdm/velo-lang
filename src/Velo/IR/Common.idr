module Velo.IR.Common

import Data.SnocList
import Decidable.Equality

import Data.List.Quantifiers

import Velo.Types
import public Toolkit.Item
import Data.SnocList.Quantifiers

import Toolkit.Data.Comparison.Informative

%default total

public export
Name : Type
Name = String

------------------------------------------------------------------------
-- The type of primitive operations

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

public export
funTy : {tys : _} -> Prim tys ty -> Ty
funTy {tys = [TyFunc dom cod, dom]} App = TyFunc dom cod
funTy _ = TyNat

public export
tag : Prim tys ty -> Nat
tag Zero = 0
tag Plus = 1
tag Add = 2
tag True = 3
tag False = 4
tag And = 5
tag App = 6

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

  public export
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

  public export
  {tys : List Ty} -> DecEq (Prim tys ty) where
    decEq p q = case hetDecEq p q of
      Yes (_, _, eq) => Yes eq
      No neq => No (\ eq => neq (Refl, Refl, eq))



public export
{tys1, tys2 : _} -> Comparable (Prim tys1 ty1) (Prim tys2 ty2) where
  cmp p@_ q@_ with (headSim p q)
    _ | Just Zero = EQ
    _ | Just Plus = EQ
    _ | Just Add = EQ
    _ | Just True = EQ
    _ | Just False = EQ
    _ | Just And = EQ
    cmp p@App q@App | Just App with (cmp (funTy p) (funTy q))
      _ | LT = LT
      _ | EQ = EQ
      _ | GT = GT
    _ | Nothing = believe_me (cmp (tag p) (tag q))

------------------------------------------------------------------------
-- The type of meta variables

public export
record Meta where
  constructor MkMeta
  metaName : Name
  {0 metaScope : SnocList Ty}
  metaScopeNames : All Item metaScope
  metaType : Ty

public export
data HasName : Name -> Meta -> Type where
  HN : (prf : x = y)
    -> HasName x (MkMeta y ns type)

hasName : (n : Name)
       -> (m : Meta)
            -> Dec (HasName n m)
hasName n m with (decEq n (metaName m))
  hasName n (MkMeta metaName metaScopeNames metaType) | (Yes prf)
    = Yes (HN prf)
  hasName n m | (No no)
    = No (\(HN Refl) => no Refl)

-- TODO Move ElemP from other project...
get : (n : Name) -> (ms : List Meta) -> Dec (Any (HasName n) ms)
get n ms with (any (hasName n) ms)
  get n ms | (Yes prf)
    = Yes prf
  get n ms | (No contra)
    = No contra

extract : (ms : List Meta) -> List.Quantifiers.Any.Any (HasName n) ms -> Meta
extract (x :: xs) (Here a)
  = x
extract (x :: xs) (There ltr)
  = extract xs ltr

export
getByName : (n  : String)
         -> (ms : List Meta)
         -> Maybe Meta
getByName n ms
  = case get n ms of
      No _ => Nothing
      Yes prf => Just (extract ms prf)

export
Show (Prim tys ty) where
  show Zero = "zero"
  show Plus = "inc"
  show Add = "add"
  show True = "true"
  show False = "false"
  show And = "and"
  show App = "apply"

-- [ EOF ]
