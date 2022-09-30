module Velo.Elaborator.Holey

import Data.DPair
import Data.SnocList.Quantifiers
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

import Velo.IR.AST
import Velo.IR.Holey

%default total

isVar : FileContext ->
        (ctxt : List Ty) ->
        All (\ _ => String) ctxt ->
        String ->
        Velo (ty : Ty ** IsVar ctxt ty)
isVar fc [] [] nm = throwAt fc (NotBound nm)
isVar fc (ty :: tys) (x :: xs) nm = case decEq x nm of
  Yes Refl => pure (ty ** V 0 Here)
  No _ => bimap id shift <$> isVar fc tys xs nm

export
check : {ctxt : List Ty} ->
        All (\ _ => String) ctxt ->
        (ty : Ty) ->
        Raw ->
        Velo (holes : List (HoleIn ctxt) ** Holey ctxt holes ty)

export
synth : {ctxt : List Ty} ->
        All (\ _ => String) ctxt ->
        Raw ->
        Velo (ty : Ty ** holes : List (HoleIn ctxt) ** Holey ctxt holes ty)

check scp ty (Hole fc nm)
  = pure ([MkHoleIn fc nm [<] [<] ty] ** Met nm)
check scp ty (Let fc x e t)
  = do (dom ** holes2 ** e) <- synth scp e
       (holes1 ** t) <- check {ctxt = ctxt += dom} (x :: scp) ty t
       let (holes1 ** stp) = steps x holes1
       (holes ** mg) <- merge fc holes1 holes2
       pure (holes ** Call App (Cons (Fun stp t) mg (Cons e NilR Empty)))
check scp ty (Fun fc x ty' t)
  = do TyFunc dom cod <- isTyFunc fc ty
       Refl <- compare fc dom ty'
       (holes ** t) <- check {ctxt = ctxt += dom} (x :: scp) cod t
       let (holes ** stp) = steps x holes
       pure (holes ** Fun stp t)
check scp ty (App fc f t)
  = do (dom ** holes2 ** t) <- synth scp t
       (holes1 ** f) <- check scp (TyFunc dom ty) f
       (holes ** mg) <- merge fc holes1 holes2
       pure (holes ** Call App (Cons f mg (Cons t NilR Empty)))
check scp ty t
  = do let fc = getFC t
       (ty' ** holes ** t) <- synth scp t
       Refl <- compare fc ty ty'
       pure (holes ** t)

synth scp (Ref fc str)
  = do (ty ** v) <- isVar fc ctxt scp str
       pure (ty ** [] ** Var v)
synth scp (Hole fc str) = throwAt fc (Hole str)
synth scp (Zero fc)
  = pure (TyNat ** [] ** Call Zero Empty)
synth scp (Plus fc m)
  = do (holes ** m) <- check scp TyNat m
       pure (TyNat ** holes ** Call Plus (Cons m NilR Empty))
synth scp (Add fc m n)
  = do (holes1 ** m) <- check scp TyNat m
       (holes2 ** n) <- check scp TyNat n
       (holes ** mg) <- merge fc holes1 holes2
       pure (TyNat ** holes ** Call Add (Cons m mg (Cons n NilR Empty)))
synth scp (T fc)
  = pure (TyBool ** [] ** Call True Empty)
synth scp (F fc)
  = pure (TyBool ** [] ** Call False Empty)
synth scp (And fc b c)
  = do (holes1 ** b) <- check scp TyBool b
       (holes2 ** c) <- check scp TyBool c
       (holes ** mg) <- merge fc holes1 holes2
       pure (TyBool ** holes ** Call And (Cons b mg (Cons c NilR Empty)))
synth scp (Let fc x e t)
  = do (dom ** holes2 ** e) <- synth scp e
       (cod ** holes1 ** t) <- synth {ctxt = ctxt += dom} (x :: scp) t
       let (holes1 ** stp) = steps x holes1
       (holes ** mg) <- merge fc holes1 holes2
       pure (cod ** holes ** Call App (Cons (Fun stp t) mg (Cons e NilR Empty)))
synth scp (Fun fc x ty t)
  = do (cod ** holes ** t) <- synth {ctxt = ctxt += ty} (x :: scp) t
       let (holes ** stp) = steps x holes
       pure (TyFunc ty cod ** holes ** Fun stp t)
synth scp (App fc f t)
  = do (ty ** holes1 ** f) <- synth scp f
       TyFunc dom cod <- isTyFunc fc ty
       (holes2 ** t) <- check scp dom t
       (holes ** mg) <- merge fc holes1 holes2
       pure (cod ** holes ** Call App (Cons f mg (Cons t NilR Empty)))
synth scp (The fc ty t)
  = do (holes ** t) <- check scp ty t
       pure (ty ** holes ** t)
