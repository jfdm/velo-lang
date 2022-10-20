||| How to replace things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Reductions

import Decidable.Equality

import Data.DPair
import Data.SnocList

import Toolkit.Decidable.Informative

import Toolkit.DeBruijn.Variable
import Toolkit.DeBruijn.Context
import Toolkit.DeBruijn.Renaming
import Toolkit.DeBruijn.Substitution
import Toolkit.Item

%default total

public export
interface Substitute type term
       => Reducible (0 type : Type)
                    (0 term : SnocList type -> type -> Type)
                            | term
  where
    data Redux : {0 ctxt : SnocList type}
              -> {0 ty   : type}
              -> (this   : term ctxt ty)
              -> (that   : term ctxt ty)
                        -> Type

public export
data Reduces : Reducible type term
            -> (  this : term ctxt ty)
            -> (  that : term ctxt ty)
                      -> Type
  where
    Refl : (r : Reducible type term)
        => {this : term ctxt ty}
                -> Reduces r this this

    Trans : (r : Reducible ty term)
         => {this, that, end : term ctxt type}
         -> Redux     this that
         -> Reduces r      that   end
         -> Reduces r this        end


-- [ EOF ]
