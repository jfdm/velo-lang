module Velo.IR.Holey

import Data.List.Quantifiers
import Decidable.Equality

import Toolkit.Data.List.Pointwise
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Variable

import Velo.Core
import Velo.Types
import Velo.IR.Common
import Velo.Elaborator.Common

%default total

------------------------------------------------------------------------
-- Type of holes

public export
record HoleIn (ctxt : SnocList Ty) where
  constructor MkHoleIn
  locations : FileContext
  holeName : Name
  ||| A hole in a context may also refer to additional local variables
  ||| because it occured under some binders we have now crossed. Its
  ||| actual scope is therefore:
  |||   localExtension <>> ctxt
  ||| See `Stepped` for what happens when we step across a binder,
  ||| and `Conflict` for what happens when there are conflicting
  ||| occurrences of the hole appearing in different local extensions.
  {localExtension : List Ty}
  localNames : All Item localExtension
  holeType : Ty

------------------------------------------------------------------------
-- Relations describing the hole transformations when walking the tree

namespace Stepped

  ||| When we step across a binder, we need to move the bound variable
  ||| to the local extension. We have picked the representation so that
  ||| the scope will match on the nose after stepping because:
  |||   localExtension <>> (ctxt += a)
  |||   (localExtension :< a) <>> ctxt
  ||| are equal by computation
  public export
  data Stepped : (a : Ty) -> HoleIn (ctxt :< a) -> HoleIn ctxt -> Type where
    MkHoleIn : Stepped a (MkHoleIn fc nm           xs  ty)
                         (MkHoleIn fc nm (I x a :: xs) ty)

  export
  step : Name ->
         {dom : _} -> (h : HoleIn (ctxt :< dom)) ->
         (h' : _ ** Stepped dom h h')
  step x (MkHoleIn fc nm xs ty)
    = (MkHoleIn fc nm (I x dom :: xs) ty ** MkHoleIn)

  export
  steps : Name ->
          {dom : _} -> (holes : List (HoleIn (ctxt :< dom))) ->
          (holes' : _ ** Pointwise (Stepped dom) holes holes')
  steps x [] = ([] ** [])
  steps x (h :: holes)
    = let (h' ** p) = step x h
          (holes' ** ps) = steps x holes
      in (h' :: holes' ** p :: ps)

namespace Conflict

  ||| When there are different occurrences of the same hole in separate
  ||| subtrees, we need to flush the local extensions as terms cannot
  ||| possibly refer to variables bound in another branch of the tree.
  public export
  data Conflict : (h, h1, h2 : HoleIn ctxt) -> Type where
    MkHoleIn :
      (nm : Name) -> (ty : Ty) -> {ext1, ext2 : _} ->
      {0 xs1 : All Item ext1} ->
      {0 xs2 : All Item ext2} ->
      Conflict (MkHoleIn fc1 nm [] ty) -- arbitrary choice: fc1
               (MkHoleIn fc1 nm xs1 ty)
               (MkHoleIn fc2 nm xs2 ty)

namespace Merged

  ||| `Merged` ensures we keep all the holes we have discovered in separate
  ||| subtrees.
  ||| The unenforced invariant is that we keep lists of holes sorted by
  ||| their name. Provided that holes1 & holes2 satisfy this invariant,
  ||| holes should also.
  public export
  data Merged : (holes, holes1, holes2 : List (HoleIn ctxt)) -> Type where
    NilL : Merged holes [] holes
    NilR : Merged holes holes []
    Both : Conflict h h1 h2 ->
           Merged holes holes1 holes2 ->
           Merged (h :: holes) (h1 :: holes1) (h2 :: holes2)
    ConL : -- invariant: h1.name < h2.name
           Merged holes holes1 holes2 ->
           Merged (h1 :: holes) (h1 :: holes1) holes2
    ConR : -- invariant: h1.name > h2.name
           Merged holes holes1 holes2 ->
           Merged (h2 :: holes) holes1 (h2 :: holes2)

  export
  merge : FileContext ->
          (holes1, holes2 : List (HoleIn ctxt)) ->
          Velo (holes ** Merged holes holes1 holes2)
  merge fc [] holes2 = pure (holes2 ** NilL)
  merge fc holes1 [] = pure (holes1 ** NilR)
  merge fc
    (MkHoleIn fc1 nm1 xs1 ty1 :: holes1)
    (MkHoleIn fc2 nm2 xs2 ty2 :: holes2)
    = case decEq nm1 nm2 of
        Yes Refl =>
          do Refl <- compare fc ty1 ty2 -- TODO: add during info
             (holes ** mg) <- merge fc holes1 holes2
             pure (_ :: holes ** Both (MkHoleIn _ _) mg)
        No _ => if nm1 < nm2
          then do (holes ** mg) <- assert_total (merge fc holes1 (MkHoleIn fc2 nm2 xs2 ty2 :: holes2))
                  pure (_ :: holes ** ConL mg)
          else do (holes ** mg) <- assert_total (merge fc (MkHoleIn fc1 nm1 xs1 ty1 :: holes1) holes2)
                  pure (_ :: holes ** ConR mg)

------------------------------------------------------------------------
-- Intermediate representation collecting its holes

data Holey : (ctxt : SnocList Ty) -> List (HoleIn ctxt) -> Ty -> Type
data Holeys : (ctxt : SnocList Ty) -> List (HoleIn ctxt) -> List Ty -> Type

public export
data Holey : (ctxt : SnocList Ty) -> List (HoleIn ctxt) -> Ty -> Type where
  Var : IsVar ctxt ty -> Holey ctxt [] ty
  Met : (nm : Name) -> Holey ctxt [MkHoleIn fc nm [] ty] ty
  Fun : Pointwise (Stepped a) holes1 holes2 ->
        Holey (ctxt :< a) holes1 b ->
        Holey ctxt holes2 (TyFunc a b)
  Call : {tys : _} ->
         Prim tys ty ->
         Holeys ctxt holes tys ->
         Holey ctxt holes ty

public export
data Holeys : (ctxt : SnocList Ty) -> List (HoleIn ctxt) -> List Ty -> Type where
  Empty : Holeys ctxt [] []
  Cons : Holey ctxt holes1 ty ->
         Merged holes holes1 holes2 ->
         Holeys ctxt holes2 tys ->
         Holeys ctxt holes (ty :: tys)
