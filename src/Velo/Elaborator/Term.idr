module Velo.Elaborator.Term

import Data.DPair
import Decidable.Equality

import Toolkit.Data.List.Pointwise
import Toolkit.Data.List.Quantifiers
import Toolkit.Data.SnocList.Quantifiers
import Toolkit.Data.List.Subset
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Variable

import Velo.Core
import Velo.Types
import Velo.IR.Common
import Velo.Elaborator.Common

import Velo.IR.Holey
import Velo.IR.Term

%default total

------------------------------------------------------------------------
-- Invariants used during elaboration

namespace HoleIn

  ||| A meta is a good representation of a hole if
  ||| 1. they have the same name
  ||| 2. they have the same type
  ||| 3. the scope of the meta embeds in that of the hole
  public export
  data Invariant : (ctxt : List Ty) -> HoleIn ctxt -> Meta -> Type where
    MkInvariant : Thinning scp (ext <>> ctxt) ->
                  Invariant ctxt
                    (MkHoleIn fc nm ext nms ty)
                    (MkMeta nm scp xs ty)

  ||| When we initialise a meta based on an existing Hole, we pick the biggest
  ||| scope possible
  export
  initInvariant :
    (ctxt : List Ty) -> (nms : All (\ _ => String) ctxt) ->
    (hole : HoleIn ctxt) ->
    (meta : Meta ** Invariant ctxt hole meta)
  initInvariant ctxt nms (MkHoleIn fc nm scp xs ty)
    = (MkMeta nm (scp <>> ctxt) (xs <>> nms) ty ** MkInvariant Keeps)

  ||| If we step across a binder, the invariant still holds
  export
  step : Stepped a h h1 -> Invariant ctxt h1 m -> Invariant (ctxt += a) h m
  step MkHoleIn (MkInvariant th) = MkInvariant th

  ||| If we step into separate subtrees, we can adapt the invariant to get
  ||| versions that work in each of the subtrees
  export
  unconflict : Conflict h h1 h2 ->
               Invariant ctxt h m ->
               (Invariant ctxt h1 m, Invariant ctxt h2 m)
  unconflict (MkHoleIn nm ty) (MkInvariant th)
    = (MkInvariant (Skips th), MkInvariant (Skips th))

namespace HolesIn

  ||| A list of metas adequately corresponds to a list of holes if there is a subset
  ||| of the metas that satisfy `HoleIn.Invariant`.
  public export
  data Invariant : (ctxt : List Ty) -> List (HoleIn ctxt) -> List Meta -> Type where
    Nil  : Invariant ctxt [] []
    Skip : Invariant ctxt holes metas ->
           Invariant ctxt holes (m :: metas)
    (::) : Invariant ctxt h m ->
           Invariant ctxt holes metas ->
           Invariant ctxt (h :: holes) (m :: metas)

  ||| Any list of metas will do for an empty list of holes
  export
  Skips : {metas : List Meta} -> Invariant ctxt [] metas
  Skips {metas = []} = []
  Skips {metas = m :: metas} = Skip Skips

  export
  initInvariant :
    (ctxt : List Ty) -> All (\ _ => String) ctxt ->
    (holes : List (HoleIn ctxt)) ->
    (metas : List Meta ** Invariant ctxt holes metas)
  initInvariant ctxt nms [] = ([] ** [])
  initInvariant ctxt nms (hole :: holes)
    = let (m ** inv) = initInvariant ctxt nms hole
          (ms ** invs) = initInvariant ctxt nms holes
      in (m :: ms ** inv :: invs)

  export
  step : Pointwise (Stepped a) holes1 holes ->
         Invariant ctxt holes metas ->
         Invariant (ctxt += a) holes1 metas
  step [] [] = []
  step pw (Skip invs) = Skip (step pw invs)
  step (stp :: xs) (inv :: invs) = step stp inv :: step xs invs

  export
  unmerge : {metas : _} ->
            Merged holes holes1 holes2 ->
            Invariant ctxt holes metas ->
            (Invariant ctxt holes1 metas, Invariant ctxt holes2 metas)
  unmerge mg (Skip inv) = bimap Skip Skip (unmerge mg inv)
  unmerge NilL inv = (Skips, inv)
  unmerge NilR inv = (inv, Skips)
  unmerge (Both cflt mg) (inv :: invs)
    = let (inv1, inv2) = unconflict cflt inv in
      let (invs1, invs2) = unmerge mg invs in
      (inv1 :: invs1, inv2 :: invs2)
  unmerge (ConL mg) (inv :: invs) = bimap (inv ::) Skip (unmerge mg invs)
  unmerge (ConR mg) (inv :: invs) = bimap Skip (inv ::) (unmerge mg invs)


------------------------------------------------------------------------
-- This elaboration step is total thanks to the invariants we maintained

namespace Meta
  export
  wscoped : Invariant ctxt [MkHoleIn fc nm [<] [<] ty] metas ->
            Exists {type = (scp : List Ty ** All (\ _ => String) scp)}
              $ \ hd => (IsVar metas (MkMeta nm hd.fst hd.snd ty), Thinning hd.fst ctxt)
  wscoped (Skip inv)
    = let Evidence _ (v, th) = wscoped inv in
      Evidence ? (shift v, th)
  wscoped (MkInvariant th :: _) = Evidence (? ** ?) (V 0 Here, th)

export
wscoped : {metas : _} ->
          Holey ctxt holes ty ->
          Invariant ctxt holes metas ->
          Term metas ctxt ty
wscopeds : {metas : _} ->
           Holeys ctxt holes tys ->
           Invariant ctxt holes metas ->
           All (Term metas ctxt) tys

wscoped (Var x) inv = Var x
wscoped (Met nm) inv = let Evidence _ (v, th) = wscoped inv in Met v th
wscoped (Fun pw b) inv = Fun (wscoped b (step pw inv))
wscoped (Call p args) inv = Call p (wscopeds args inv)

wscopeds Empty inv = []
wscopeds (Cons arg mg args) inv
  = let (inv1, inv2) = unmerge mg inv in
    wscoped arg inv1 :: wscopeds args inv2
