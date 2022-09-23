||| How to rename things
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Renaming

import Decidable.Equality
import Data.DPair

import Toolkit.Decidable.Informative

import Toolkit.Data.List.AtIndex
import Toolkit.Data.DList
import Toolkit.Data.DList.AtIndex

import Toolkit.DeBruijn.Context
import public Toolkit.DeBruijn.Variable

%default total


public export
interface Rename (type : Type) (term : List type -> type -> Type) | term where
  rename : {old, new : List type}
        -> (f : {ty : type} -> IsVar old ty
                            -> IsVar new ty)
        -> ({ty : type} -> term old ty
                        -> term new ty)

  %inline
  embed : {ty   : type}
       -> {ctxt : List type}
               -> IsVar ctxt ty
               -> term  ctxt ty

public export
%inline
weakens : {type : Type}
       -> {term : List type -> type -> Type}
       -> Rename type term
       => {old, new : List type}
       -> (f : {ty  : type}
                   -> IsVar old ty
                   -> term  new ty)
       -> ({ty,type' : type}
              -> IsVar (old += type') ty
              -> term  (new += type') ty)

weakens f (V 0 Here)
  = embed (V Z Here)
weakens f (V (S idx) (There later))
  = rename shift (f (V idx later))

-- [ EOF ]
