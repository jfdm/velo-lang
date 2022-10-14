|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Context

import Decidable.Equality

import Data.DPair
import Data.Singleton

import Toolkit.Decidable.Informative

import public Toolkit.Data.List.AtIndex
import public Toolkit.Data.DList
import Toolkit.Data.DList.AtIndex

import public Toolkit.Item

%default total

-- A reverse cons operator.
infixr 6 +=

namespace List
  ||| Append `x` to the head of `xs`.
  public export
  (+=) : List a -> a -> List a
  (+=) xs x = x :: xs

public export
Context : (kind : Type) -> (types : List kind) -> Type
Context kind = DList kind Item

export
extend : (ctxt  : Context kind types)
      -> (label : String)
      -> (type  : kind)
               -> Context kind (types += type)
extend ctxt label type
  = I label type :: ctxt

export
(+=) : (ctxt  : Context kind types)
    -> (label : String)
    -> (type  : kind)
             -> Context kind (types += type)
(+=) = extend

||| A quantifier over the context that the given predicate holds.
|||
||| This is modelled after De Bruijn indices, and the underlying
||| quantifier is `Any`.
|||
public export
data Exists : (kind : Type)
           -> (pred  : (type : kind) -> Type)
           -> (key   : String)
           -> {types : List kind}
           -> (ctxt  : Context kind types)
                    -> Type
  where
    E : {ctxt : Context kind types}
     -> {pred : (type : kind) -> Type}
     -> (type : kind)
     -> (item : Item type)
     -> (prf  : pred type)
     -> {loc  : Nat}
     -> (locC : HoldsAtIndex kind Item (Holds kind pred key) ctxt loc)
     -> (locN : AtIndex type types loc)
             -> Exists kind pred key ctxt

export
deBruijn : {ctxt : Context kind types}
        -> (prf  : Exists kind pred key ctxt)
                -> (type ** DPair Nat (AtIndex type types))
deBruijn (E type item prf locC locN)
  = (type ** _ ** locN)

namespace Exists
  public export
  data Error type = NotFound
                  | NotSatisfied type

isEmpty : Exists kind pred key [] -> Void
isEmpty (E _ _ _ (Here x) _) impossible
isEmpty (E _ _ _ (There contra later) _) impossible

notLater : (Holds  kind pred key  h      -> Void)
        -> (Exists kind pred key       t -> Void)
        ->  Exists kind pred key (h :: t)
        -> Void
notLater f g (E type item prf (Here x) locN) = f x
notLater f g (E type item prf (There contra later) (There x)) = g (E type item prf later x)

export
exists : {kind  : Type}
      -> {types : List kind}
      -> {pred  : (type : kind) -> Type}
      -> (func  : (type : kind) -> DecInfo err (pred type))
      -> (key   : String)
      -> (ctxt  : Context kind types)
               -> DecInfo (Exists.Error err)
                          (Exists kind pred key ctxt)

exists f _ []
  = No NotFound
       isEmpty
exists f key (head :: tail) with (holds f key head)
  exists f key ((I str x) :: tail) | (Yes (H prfK prf))
    = Yes (E _ (I str x) prf (Here (H prfK prf)) Here)

  exists f key (head :: tail) | (No msg contra) with (exists f key tail)
    exists f key (head :: tail) | (No msg contra) | (Yes (E type item prf locC locN))
      = Yes (E type item prf (There contra locC) (There locN))

    -- [ Note ]
    --
    -- we need to ensure that the 'correct' error message has been satisfied.
    exists f key (head :: tail) | (No (NotSatisfied x) contra) | (No msgR contraR)
      = No (NotSatisfied x)
           (notLater contra contraR)
    exists f key (head :: tail) | (No (WrongName x y) contra) | (No msgR contraR)
      = No msgR
           (notLater contra contraR)


namespace Lookup

  public export
  IsBound : {kind  : Type}
         -> {types : List kind}
         -> (key   : String)
         -> (ctxt  : Context kind types)
                  -> Type
  IsBound {kind} str ctxt
    = Exists kind Singleton
                str
                ctxt

  single : (item : kind)
                -> DecInfo () (Singleton item)
  single item = Yes (Val item)


  export
  lookup : {kind  : Type}
        -> {types : List kind}
        -> (str   : String)
        -> (ctxt  : Context kind types)
                 -> DecInfo (Exists.Error ())
                            (IsBound str ctxt)
  lookup = exists single

-- [ EOF ]
