||| How to rename things
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Renaming

import Toolkit.Data.SnocList.AtIndex
import public Toolkit.DeBruijn.Variable

%default total


public export
interface Rename (type : Type) (term : SnocList type -> type -> Type) | term where
  rename : {old, new : SnocList type}
        -> (f : {ty : type} -> IsVar old ty
                            -> IsVar new ty)
        -> ({ty : type} -> term old ty
                        -> term new ty)

  %inline
  embed : {ty   : type}
       -> {ctxt : SnocList type}
               -> IsVar ctxt ty
               -> term  ctxt ty

public export
%inline
weakens : {type : Type}
       -> {term : SnocList type -> type -> Type}
       -> Rename type term
       => {old, new : SnocList type}
       -> (f : {ty  : type}
                   -> IsVar old ty
                   -> term  new ty)
       -> ({ty,type' : type}
              -> IsVar (old :< type') ty
              -> term  (new :< type') ty)

weakens f v@_ with (view v)
  _ | Here
    = embed here
  _ | There w
    = rename shift (f w)

-- [ EOF ]
