||| Data structure to compute de Bruijn indices.
|||
||| Thanks to David Christiansen's Galois tutorials for the accessor and
||| mutator functions for environments/object store.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.DeBruijn

import public Decidable.Equality

import public Data.List.Elem

import public Toolkit.Data.DList

%default total

-- A reverse cons operator.
infixr 6 +=

namespace List

  ||| Proof that the given list (`xs`) contains the given element
  ||| (`x`).
  |||
  |||
  public export
  Contains : List a -> a -> Type
  Contains xs x = Elem x xs

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : List a -> a -> List a
  (+=) xs x = x :: xs


||| A De Bruijn Index.
|||
||| @T    The type of type's collected.
||| @ctxt The collection of types.
||| @t    The element collected at the current position.
public export
Index : (type : Type)
     -> (ctxt : List type)
     -> (t    : type)
             -> Type
Index _ ctxt t = Elem t ctxt


||| Sometimes it is bettern to think that we have this thing called an
||| environment and not a `DList`.
|||
||| @t    The Type for Types in our environment.
||| @obj  How we interpret the types in our DSL. Either this is a
|||       dependent type or a function that computes a type.
||| @ctxt The typing context.
public export
Env : (t : Type) -> (obj : t -> Type) -> (ctxt : List t) -> Type
Env ty obj ctxt = DList ty obj ctxt

||| Add an object from our typing environment.
||| @env The typing environment.
export
extend : {t : ty}
      -> (env : Env ty e ctxt)
      -> (obj : e t)
      -> Env ty e (t::ctxt)
extend env obj = obj :: env

||| Read an object from our typing environment.
|||
||| @idx The typing context.
||| @env The typing environment.
export
read : (idx : Index ty ctxt t)
    -> (env : Env ty e ctxt)
    -> e t
read Here      (obj::store) = obj
read (There x) (obj::store) = read x store

||| Add an object to our typnig environment.
|||
||| @idx The typing context.
||| @obj The object to add.
||| @env The environment to which the object is added.
export
update : (idx : Index ty ctxt t )
      -> (obj : e t)
      -> (env : Env ty e ctxt)
      -> Env ty e ctxt
update Here      obj (_    :: store) = obj  :: store
update (There x) obj (obj' :: store) = obj' :: update x obj store

namespace KV


  public export
  indexEmpty : {k : String}
            -> (t ** Index (String, type) [] (k, t))
            -> Void
  indexEmpty (MkDPair fst snd) impossible

  public export
  notInIndex : (keyContra : (k = a) -> Void)
           -> (index     : List (String, type))
           -> (kvContra  : (t : type ** Index (String, type)            xs  (k, t)) -> Void)
           -> (prf       : (t : type ** Index (String, type) ((a, b) :: xs) (k, t)))
                        -> Void
  notInIndex keyContra index kvContra (MkDPair b Here) = keyContra Refl
  notInIndex keyContra index kvContra (MkDPair fst (There x)) = kvContra (_ ** x)

  public export
  isIndex : DecEq type
         => (k : String)
         -> (ctxt : List (String, type))
         -> Dec (t : type ** Index (String, type) ctxt (k,t))
  isIndex k [] = No indexEmpty
  isIndex k ((a,b) :: xs) with (decEq k a)
    isIndex a ((a,b) :: xs) | (Yes Refl) = Yes (b ** Here)
    isIndex k ((a,b) :: xs) | (No contra) with (isIndex k xs)
      isIndex k ((a,b) :: xs) | (No contra) | (Yes (MkDPair fst snd))
        = Yes (_ ** There snd)
      isIndex k ((a,b) :: xs) | (No contra) | (No f) = No (notInIndex contra xs f)

namespace Renaming

  public export
  weaken : (func : Contains old type
                -> Contains new type)
        -> (Contains (old += type') type
         -> Contains (new += type') type)

  weaken func Here = Here
  weaken func (There rest) = There (func rest)

  public export
  interface Rename (type : Type) (term : List type -> type -> Type) | term where
    rename : {old, new : List type}
          -> (f : {ty : type} -> Contains old ty
                              -> Contains new ty)
          -> ({ty : type} -> term old ty
                          -> term new ty)

    var : {ty   : type}
       -> {ctxt : List type}
               -> Elem ty ctxt
               -> term ctxt ty


    weakens : {old, new : List type}
           -> (f : {ty  : type}
                       -> Contains old ty
                       -> term     new ty)
           -> ({ty,type' : type}
                  -> Contains (old += type') ty
                  -> term     (new += type') ty)
    weakens f Here = var Here
    weakens f (There rest) = rename There (f rest)

namespace Substitution

  namespace General
    public export
    interface Rename type term
           => Substitute (type : Type) (term : List type -> type -> Type) | term where

      subst : {old, new : List type}
           -> (f : {ty  : type}
                       -> Contains old ty
                       -> term     new ty)
           -> ({ty : type}
                  -> term old ty
                  -> term new ty)

  namespace Single

    apply : {type : Type}
         -> {term : List type -> type -> Type}
         -> Rename type term
         => {ctxt   : List type}
         -> {typeA  : type}
         -> {typeB  : type}
         -> (this   : term      ctxt    typeB)
         -> (idx    : Contains (ctxt += typeB) typeA)
                   -> term      ctxt           typeA
    apply this Here = this
    apply this (There rest) = var rest

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
      = subst (apply this) inThis

  namespace Double

    public export
    apply : {type : Type}
         -> {term : List type -> type -> Type}
         -> Rename type term
         => {ctxt          : List type}
         -> {typeA, typeB, typeC : type}
         -> (this    : term       ctxt                     typeA)
         -> (andThis : term       ctxt                     typeB)
         -> (idx     : Contains ((ctxt += typeA) += typeB) typeC)
                    -> term       ctxt                     typeC
    apply this andThis Here              = andThis
    apply this andThis (There Here)      = this
    apply this andThis (There (There x)) = var x

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

-- --------------------------------------------------------------------- [ EOF ]
