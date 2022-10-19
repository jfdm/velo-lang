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
interface Rename (0 type : Type) (0 term : SnocList type -> type -> Type) | term where
  rename : {0 old, new : SnocList type}
        -> (f : {0 ty : type} -> IsVar old ty
                              -> IsVar new ty)
        -> ({0 ty : type} -> term old ty
                          -> term new ty)

  %inline
  embed : {0 ty   : type}
       -> {0 ctxt : SnocList type}
               -> IsVar ctxt ty
               -> term  ctxt ty

public export
%inline
weakens : {0 type : Type}
       -> {0 term : SnocList type -> type -> Type}
       -> Rename type term
       => {0 old, new : SnocList type}
       -> (f : {0 ty  : type}
                   -> IsVar old ty
                   -> term  new ty)
       -> ({0 ty,type' : type}
              -> IsVar (old :< type') ty
              -> term  (new :< type') ty)

weakens f v@_ with (view v)
  _ | Here
    = embed here
  _ | There w
    = rename shift (f w)

-- [ EOF ]
