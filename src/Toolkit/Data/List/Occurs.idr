|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Occurs

import Decidable.Equality

import Toolkit.Decidable.Informative

import Toolkit.Data.Nat
import Toolkit.Data.DList
import Toolkit.Data.List.Size
import Toolkit.Data.List.Interleaving

%default total


public export
data Occurs : (type : Type)
           -> (p    : type -> Type)
           -> (xs   : List type)
           -> (cy   : Nat)
           -> (cn   : Nat)
                   -> Type
   where
     O : (thrown     : List type)
      -> (sizeThrown : Size thrown t)

      -> (kept       : List type)
      -> (sizeKept   : Size kept   k)

      -> (prfOrigin  : Interleaving kept thrown input)

      -> (prfKept    : DList  type        holdsFor  kept)
      -> (prfThrown  : DList  type (Not . holdsFor) throw)

                    -> Occurs type holdsFor input k t

namespace Result

  public export
  data Occurs : (type : Type)
             -> (p    : type -> Type)
             -> (xs   : List type)
                     -> Type
    where
      O : {type  : Type}
       -> {p     : type -> Type}
       -> (xs    : List type)
       -> (cy,cn : Nat)
       -> (prf   : Occurs type p xs cy cn)
                -> Occurs type p xs


export
occurs : {type : Type}
      -> {p    : type -> Type}
      -> (f    : (this : type) -> Dec (p this))
      -> (xs   : List type)
              -> Occurs type p xs
occurs f []
  = O [] 0 0 (O [] Zero [] Zero Empty [] [])

occurs f (x :: xs) with (f x)
  occurs f (x :: xs) | (Yes prf) with (occurs f xs)

    occurs f (x :: xs) | (Yes prf) | (O xs cy cn (O thrown sizeThrown kept sizeKept prfOrigin prfKept prfThrown))
      = O (x::xs) (S cy) cn (O thrown sizeThrown (x :: kept) (PlusOne sizeKept) (Left x prfOrigin) (prf :: prfKept) prfThrown)

  occurs f (x :: xs) | (No not) with (occurs f xs)
    occurs f (x :: xs) | (No not) | (O xs cy cn (O thrown sizeThrown kept sizeKept prfOrigin prfKept prfThrown))
      = O (x::xs) cy (S cn) (O (x :: thrown) (PlusOne sizeThrown) kept sizeKept (Right x prfOrigin) prfKept (not :: prfThrown))

-- [ EOF ]
