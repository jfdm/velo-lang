||| Naming
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Variable

import Decidable.Equality
import Data.DPair

import Toolkit.Decidable.Informative

import Toolkit.Data.List.AtIndex
import Toolkit.Data.DList
import Toolkit.Data.DList.AtIndex

import Toolkit.DeBruijn.Context

%default total

public export
data IsVar : (ctxt : List kind)
          -> (type :      kind)
                  -> Type
  where
    V : (  pos : Nat)
     -> (0 prf : AtIndex type ctxt pos)
              -> IsVar   ctxt type

public export
%inline
shift : IsVar ctxt type -> IsVar (ctxt += a) type
shift (V pos prf) = V (S pos) (There prf)

public export
%inline
weaken : (func : IsVar old type
              -> IsVar new type)
      -> (IsVar (old += type') type
       -> IsVar (new += type') type)
weaken f (V Z Here)
  = V Z Here
weaken f (V (S idx) (There later)) with (f (V idx later))
  weaken f (V (S idx) (There later)) | (V pos prf)
    = V (S pos) (There prf)


-- [ EOF ]
