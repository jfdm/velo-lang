|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Filter

import Toolkit.Data.DList
import Toolkit.Data.List.Interleaving

%default total

public export
data Filter : (holdsFor : type -> Type)
           -> (input : List type)
           -> Type
  where
    MkFilter : {thrown : List type}
            -> (kept : List type)
            -> (prfOrdering : Interleaving kept thrown input)
            -> (prfKept     : DList type holdsFor kept)
            -> (prfThrown   : DList type (Not . holdsFor) thrown)
            -> Filter holdsFor input

export
filter : (test   : (value : type) -> Dec (holds value))
      -> (input  : List type)
      -> Filter holds input
filter test [] = MkFilter [] Empty [] []
filter test (x :: xs) with (filter test xs)
  filter test (x :: xs) | (MkFilter kept prfOrdering prfKept prfThrown) with (test x)
    filter test (x :: xs) | (MkFilter kept prfOrdering prfKept prfThrown) | (Yes prf)
      = MkFilter (x::kept) (Left x prfOrdering) (prf :: prfKept) prfThrown
    filter test (x :: xs) | (MkFilter kept prfOrdering prfKept prfThrown) | (No contra)
      = MkFilter kept (Right x prfOrdering) prfKept (contra :: prfThrown)

export
extract : Filter p xs
       -> (ks ** DList type p ks)
extract (MkFilter kept prfOrdering prfKept prfThrown)
  = (kept ** prfKept)


-- [ EOF ]
