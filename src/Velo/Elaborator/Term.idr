module Velo.Elaborator.Term

import Data.DPair
import Decidable.Equality

import Toolkit.Data.List.Pointwise
import Toolkit.Data.List.Quantifiers
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

namespace Meta
  export
  wscoped : Invariant ctxt [MkHoleIn fc nm [<] ty] metas ->
            Exists (\ scp => (IsVar metas (MkMeta nm scp ty), Thinning scp ctxt))
  wscoped (Skip inv)
    = let Evidence scp (v, th) = wscoped inv in Evidence scp (shift v, th)
  wscoped (MkInvariant th :: _) = Evidence ? (V 0 Here, th)

export
wscoped : {metas : _} ->
          Holey ctxt holes ty ->
          Invariant ctxt holes metas ->
          Term ctxt metas ty
wscopeds : {metas : _} ->
           Holeys ctxt holes tys ->
           Invariant ctxt holes metas ->
           All (Term ctxt metas) tys

wscoped (Var x) inv = Var x
wscoped (Met nm) inv = let Evidence _ (v, th) = wscoped inv in Met v th
wscoped (Lam pw b) inv = Lam (wscoped b (step pw inv))
wscoped (Call p args) inv = Call p (wscopeds args inv)

wscopeds Empty inv = []
wscopeds (Cons arg args mg) inv
  = let (inv1, inv2) = unmerge mg inv in
    wscoped arg inv1 :: wscopeds args inv2
