||| How to replace things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Substitution

import Decidable.Equality

import Data.DPair

import Toolkit.Decidable.Informative

import Toolkit.Data.List.AtIndex
import Toolkit.Data.DList
import Toolkit.Data.DList.AtIndex

import Toolkit.DeBruijn.Context.Item
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming

%default total

namespace General
  public export
  interface Rename type term
         => Substitute (type : Type)
                       (term : List type -> type -> Type)
                             | term
    where

      subst : {old, new : List type}
           -> (f : {ty  : type}
                       -> IsVar old ty
                       -> term  new ty)
           -> ({ty : type}
                  -> term old ty
                  -> term new ty)

namespace Single
  %inline
  apply : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => {ctxt   : List type}
       -> {typeA  : type}
       -> {typeB  : type}
       -> (this   : term   ctxt    typeB)
       -> (idx    : IsVar (ctxt += typeB) typeA)
                 -> term   ctxt           typeA
  apply this (V Z Here) = this
  apply this (V (S pos) (There later)) = embed (V pos later)

  export
  subst : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => Substitute type term
       => {ctxt          : List type}
       -> {typeA         : type}
       -> {typeB         : type}
       -> (this          : term  ctxt           typeB)
       -> (inThis        : term (ctxt += typeB) typeA)
                        -> term  ctxt           typeA
  subst {ctxt} {typeA} {typeB} this inThis
    = General.subst (apply this) inThis

namespace Double

  %inline
  public export
  apply : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => {ctxt          : List type}
       -> {typeA, typeB, typeC : type}
       -> (this    : term    ctxt                     typeA)
       -> (andThis : term    ctxt                     typeB)
       -> (idx     : IsVar ((ctxt += typeA) += typeB) typeC)
                  -> term    ctxt                     typeC
  apply this andThis pos = ?todo -- I know

  public export
  subst : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => Substitute type term
       => {ctxt          : List type}
       -> {typeA, typeB, typeC : type}
       -> (this    : term  ctxt                     typeA)
       -> (andThis : term  ctxt                     typeB)
       -> (inThis  : term ((ctxt += typeA) += typeB) typeC)
                  -> term   ctxt                     typeC
  subst {ctxt} {typeA} {typeB} {typeC} this andThis inThis
    = General.subst (apply this andThis) inThis

-- [ EOF ]
