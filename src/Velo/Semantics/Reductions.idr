module Velo.Semantics.Reductions

import Decidable.Equality

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term
import Velo.Values

%default total

data Reduxes : {tys : List Ty} -> (these, those : All (Term metas ctxt) tys) -> Type
data Redux : (this,that : Term metas ctxt type) -> Type

infixr 7 !:

public export
data Reduxes :{tys : List Ty} -> (these, those : All (Term metas ctxt) tys)
            -> Type
  where

    (!:) : {0 tys : List Ty}
        -> (hd : Redux this that)
        -> (rest : All (Term metas ctxt) tys)
        -> Reduxes (this :: rest) (that :: rest)

    (::) : (value : Value hd)
        -> (tl : Reduxes these those)
        -> Reduxes (hd :: these) (hd :: those)

public export
data Redux : (this,that : Term metas ctxt type)
          -> Type
  where

    -- [ Call ]
    SimplifyCall : (p : Prim tys ty)
                -> (step : Reduxes these those)
                -> Redux (Call p these) (Call p those)

    -- [ Nats ]
    ReduceAddZW : (value : Value right)
                        -> Redux (Call Add [Call Zero [], right])
                                 right

    RewriteEqNatPW : (valueL : Value (Call Plus [this]))
                  -> (valueR : Value right)
                            -> Redux (Call Add [Call Plus [this], right])
                                     (Call Add [this, Call Plus [right]])


    -- [ Bool ]

    ReduceAndTT : Redux (Call And [Call True [], Call True []])
                        (Call True [])

    ReduceAndWF : Redux (Call And [left, Call False []])
                        (Call False [])

    ReduceAndFW : Redux (Call And [Call False [], right])
                        (Call False [])


    ReduceFuncApp : {body : Term metas (ctxt :< type) return}
                 -> {var  : Term metas ctxt type}
                 -> Value var
                          -> Redux (Call App [Fun body, var])
                                   (Single.subst var body)


-- [ EOF ]
