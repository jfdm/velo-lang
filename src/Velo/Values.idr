module Velo.Values

import Decidable.Equality

import Velo.Types
import Velo.Terms

%default total

public export
data Value : (term : Term ctxt type)
                  -> Type
  where
    Fun : Value (Fun body)

    Zero : Value Zero
    Plus : Value rest -> Value (Plus rest)

    True : Value True
    False : Value False

-- [ EOF ]
