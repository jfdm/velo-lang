module Velo.Semantics.Reductions

import Decidable.Equality

import Velo.Types
import Velo.Terms
import Velo.Values

%default total

public export
data Redux : (this,that : Term ctxt type)
                       -> Type
  where

    -- [ Nats ]
    SimplifyPlus : (inner : Redux this that)
                         -> Redux (Plus this) (Plus that)

    SimplifyAddLeft : (left : Redux this that)
                           -> Redux (Add this right)
                                    (Add that right)

    SimplifyAddRight : (value : Value left)
                    -> (right : Redux this that)
                             -> Redux (Add left this)
                                      (Add left that)

    ReduceAddZW : (value : Value right)
                        -> Redux (Add Zero right)
                                 right

    RewriteEqNatPW : (valueL : Value (Plus this))
                  -> (valueR : Value right)
                            -> Redux (Add (Plus this) right)
                                     ((Add this (Plus right)))


    -- [ Bool ]

    SimplifyAndLeft : (left : Redux this that)
                           -> Redux (And this right)
                                    (And that right)

    SimplifyAndRight : (value : Value left)
                    -> (right : Redux this that)
                             -> Redux (And left this)
                                      (And left that)

    ReduceAndTT : Redux (And True True)
                        True

    ReduceAndWF : Redux (And left False)
                        False

    ReduceAndFW : Redux (And False right)
                             False


    -- [ STLC ]
    SimplifyFuncAppFunc : (func : Redux this that)
                               -> Redux (App this var)
                                        (App that var)

    SimplifyFuncAppVar : {this, that : Term ctxt type}
                      -> {func       : Term ctxt (TyFunc type return)}
                      -> (value      : Value func)
                      -> (var        : Redux this that)
                                    -> Redux (App func this)
                                             (App func that)

    ReduceFuncApp : {ctxt : List Ty}
                 -> {type : Ty}
                 -> {body : Term (ctxt += type) return}
                 -> {var  : Term  ctxt    type}
                 -> Value var
                          -> Redux (App (Fun body) var)
                                   (Single.subst var body)

public export
data Reduces : (this : Term ctxt type)
            -> (that : Term ctxt type)
            -> Type
  where
    Refl  : {this : Term ctxt type}
                 -> Reduces this this

    Trans : {this, that, end : Term ctxt type}
         -> Redux this that
         -> Reduces that end
         -> Reduces this end
-- [ EOF ]
