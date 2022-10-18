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
record ElabResult where
  constructor MkElabResult
  {ty : Ty}
  metas : List Meta
  term : Term metas [<] ty

export
elab : Raw
    -> Velo ElabResult
elab ast
  = do (ty ** holes ** t) <- synth [<] ast
       let (metas ** inv) = initInvariant [<] holes
       let t = wscoped t inv
       pure (MkElabResult metas t)

-- [ EOF ]
