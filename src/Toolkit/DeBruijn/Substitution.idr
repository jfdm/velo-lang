||| How to replace things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Substitution

import Decidable.Equality

import Data.DPair

import Toolkit.Decidable.Informative

import Toolkit.DeBruijn.Variable
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming
import Toolkit.Item

%default total

namespace General
  public export
  interface Rename type term
         => Substitute (0 type : Type)
                       (0 term : SnocList type -> type -> Type)
                             | term
    where

      subst : {0 old, new : SnocList type}
           -> (f : {0 ty  : type}
                       -> IsVar old ty
                       -> term  new ty)
           -> ({0 ty : type}
                  -> term old ty
                  -> term new ty)

namespace Single
  %inline
  apply : {0 type : Type}
       -> {0 term : SnocList type -> type -> Type}
       -> Rename type term
       => {0 ctxt   : SnocList type}
       -> {0 typeA  : type}
       -> {0 typeB  : type}
       -> (this   : term   ctxt    typeB)
       -> (idx    : IsVar (ctxt :< typeB) typeA)
                 -> term   ctxt           typeA
  apply this v@_ with (view v)
    _ | Here = this
    _ | There w = embed w

  export
  subst : {0 type : Type}
       -> {0 term : SnocList type -> type -> Type}
       -> Rename type term
       => Substitute type term
       => {0 ctxt          : SnocList type}
       -> {0 typeA         : type}
       -> {0 typeB         : type}
       -> (this          : term  ctxt           typeB)
       -> (inThis        : term (ctxt :< typeB) typeA)
                        -> term  ctxt           typeA
  subst {ctxt} {typeA} {typeB} this inThis
    = General.subst (apply this) inThis

namespace Double

  %inline
  public export
  apply : {0 type : Type}
       -> {0 term : SnocList type -> type -> Type}
       -> Rename type term
       => {0 ctxt          : SnocList type}
       -> {0 typeA, typeB, typeC : type}
       -> (this    : term    ctxt                     typeA)
       -> (andThis : term    ctxt                     typeB)
       -> (idx     : IsVar ((ctxt :< typeA) :< typeB) typeC)
                  -> term    ctxt                     typeC
  apply this andThis pos@_ with (view pos)
    _ | Here = andThis
    _ | There pos' with (view pos')
      apply this andThis pos@_ | There pos'@_ | Here = this
      apply this andThis pos@_ | There pos'@_ | There pos'' = embed pos''

  public export
  subst : {0 type : Type}
       -> {0 term : SnocList type -> type -> Type}
       -> Rename type term
       => Substitute type term
       => {0 ctxt          : SnocList type}
       -> {0 typeA, typeB, typeC : type}
       -> (this    : term  ctxt                     typeA)
       -> (andThis : term  ctxt                     typeB)
       -> (inThis  : term ((ctxt :< typeA) :< typeB) typeC)
                  -> term   ctxt                     typeC
  subst {ctxt} {typeA} {typeB} {typeC} this andThis inThis
    = General.subst (apply this andThis) inThis

-- [ EOF ]
