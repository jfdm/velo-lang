module Velo.Values

import Decidable.Equality

import Velo.Types
import Velo.Terms

%default total

public export
data ValuePrim : (op : Prim tys ty)
              -> Type
  where
    Zero : ValuePrim Zero
    Plus : ValuePrim Plus
    True : ValuePrim True
    False : ValuePrim False

public export
data ComputePrim : (op : Prim tys ty)
              -> Type
  where
    Add : ComputePrim Add
    And : ComputePrim And
    App : ComputePrim App

public export
isValuePrim : (op : Prim tys ty)
           -> Either (ValuePrim op) (ComputePrim op)
isValuePrim Zero = Left Zero
isValuePrim Plus = Left Plus
isValuePrim Add = Right Add
isValuePrim True = Left True
isValuePrim False = Left False
isValuePrim And = Right And
isValuePrim App = Right App

data Values : (args : All (Term ctxt) tys) -> Type
data Value : (term : Term ctxt type) -> Type

public export
data Values : (args : All (Term ctxt) tys)
           -> Type
  where

    Nil : Values []
    (::) : (value : Value t)
        -> (values : Values ts)
        -> Values (t :: ts)

public export
data Value : (term : Term ctxt type)
          -> Type
  where
    Fun : Value (Fun body)

    Call : (prim : ValuePrim op)
        -> (values : Values ts)
        -> Value (Call op ts)


-- [ EOF ]
