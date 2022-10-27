module Velo.Elaborator

import Data.List
import Data.DPair
import Data.SnocList.Quantifiers
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

import Velo.IR.AST

import Velo.IR.Holey
import Velo.IR.Term

import Velo.Elaborator.Holey
import Velo.Elaborator.Term

%default total

public export
data IsEmpty : (xs : List a) -> Type where
  ItIsEmpty : IsEmpty Nil


Uninhabited (IsEmpty (x::xs)) where
  uninhabited ItIsEmpty impossible

-- @TODO Merge into Toolkit or Idris2
nonEmpty : (xs : List a) -> DecInfo (IsEmpty xs) (NonEmpty xs)
nonEmpty []
  = No ItIsEmpty absurd

nonEmpty (x :: xs)
  = Yes IsNonEmpty

public export
record SynthResult (ctxt : SnocList Ty) where
  constructor MkSynthResult
  {ty : Ty}
  metas : List Meta
  term : Term metas ctxt ty

namespace Synth

  export
  elab : All Item ctxt
      -> Raw
      -> Velo (SynthResult ctxt)
  elab gam ast
    = do (ty ** holes ** t) <- synth gam ast
         let (metas ** inv) = initInvariant gam holes
         let t = wscoped t inv
         pure (MkSynthResult metas t)

public export
record CheckResult (ctxt : SnocList Ty) (ty : Ty) where
  constructor MkCheckResult
  metas : List Meta
  term : Term metas ctxt ty

namespace Check

  export
  elab : All Item ctxt
      -> (ty : Ty)
      -> Raw
      -> Velo (CheckResult ctxt ty)
  elab gam ty ast
    = do (holes ** t) <- check gam ty ast
         let (metas ** inv) = initInvariant gam holes
         let t = wscoped t inv
         pure (MkCheckResult metas t)

-- [ EOF ]
