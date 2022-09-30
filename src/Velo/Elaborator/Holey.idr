module Velo.Elaborator.Holey

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

{-
check : {ctxt : List Ty} ->
        All (\ _ => String) ctxt ->
        (ty : Ty) ->
        Check ->
        Maybe (holes : List (HoleIn ctxt) ** Holey ctxt holes ty)

synth : {ctxt : List Ty} ->
        All (\ _ => String) ctxt ->
        Synth ->
        Maybe (ty : Ty ** holes : List (HoleIn ctxt) ** Holey ctxt holes ty)

check scp ty (Met nm) = Just (_ ** Met nm)
check scp ty (Lam x b)
  = do TyFunc dom cod <- isTyFunc ty
       (holes ** b) <- check {ctxt = dom :: ctxt} (x :: scp) cod b
       let (holes ** stepped) = steps holes
       pure (holes ** Lam stepped b)
check scp ty (Emb s)
  = do (ty' ** holes ** tm) <- synth scp s
       case decEq ty ty' of
         Yes Refl => pure (holes ** tm)
         No _ => Nothing

synth scp (Var v)
  = do (ty ** v) <- isVar _ scp v
       pure (ty ** [] ** Var v)
synth scp (Cut t ty)
  = do (holes ** t) <- check scp ty t
       pure (ty ** holes ** t)
synth scp (App f t)
  = do (ty ** holes1 ** f) <- synth scp f
       TyFunc dom cod <- isTyFunc ty
       (holes2 ** t) <- check scp dom t
       (holes ** mg) <- merge holes1 holes2
       pure (cod ** holes ** App f t mg)
-}
