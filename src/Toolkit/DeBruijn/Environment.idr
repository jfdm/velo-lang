||| Environments.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Environment

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

||| Sometimes it is bettern to think that we have this thing called an
||| environment and not a `DList`.
|||
||| @t    The Type for Types in our environment.
||| @obj  How we interpret the types in our DSL. Either this is a
|||       dependent type or a function that computes a type.
||| @ctxt The typing context.
public export
Env : (t : Type) -> (obj : t -> Type) -> (ctxt : List t) -> Type
Env = DList

||| Add an object to our execution environment.
||| @env The typing environment.
export
extend : {t : ty}
      -> (env : Env ty e ctxt)
      -> (obj : e t)
      -> Env ty e (t::ctxt)
extend env obj = obj :: env

namespace Elem
  ||| Read an object from our typing environment.
  |||
  ||| @idx Which object.
  ||| @env The execution environment.
  export
  read : (idx : Elem t ctxt)
      -> (env : Env ty e ctxt)
      -> e t
  read Here      (obj::store) = obj
  read (There x) (obj::store) = read x store

  ||| Add an object to our execution environment.
  |||
  ||| @idx Where the object is.
  ||| @obj The new object.
  ||| @env The environment to which the object is added.
  export
  update : (idx : Elem t ctxt)
        -> (obj : e t)
        -> (env : Env ty e ctxt)
        -> Env ty e ctxt
  update Here      obj (_    :: store) = obj  :: store
  update (There x) obj (obj' :: store) = obj' :: update x obj store

namespace IsVar
  ||| Read an object from our typing environment.
  |||
  ||| @idx Which object.
  ||| @env The execution environment.
  export
  read : (idx : IsVar ctxt t)
      -> (env : Env ty e ctxt)
      -> e t
  read (V 0 Here) (elem :: rest)
    = elem
  read (V (S idx) (There later)) (elem :: rest)
    = read (V idx later) rest

  ||| Add an object to our execution environment.
  |||
  ||| @idx Where the object is.
  ||| @obj The new object.
  ||| @env The environment to which the object is added.
  export
  update : (idx : IsVar ctxt t)
        -> (obj : e t)
        -> (env : Env ty e ctxt)
        -> Env ty e ctxt
  update (V 0 Here) obj (elem :: rest)
    = obj :: rest
  update (V (S k) (There later)) obj (elem :: rest)
    = elem :: update (V k later) obj rest

-- [ EOF ]
