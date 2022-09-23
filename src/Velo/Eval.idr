module Velo.Eval

import Velo.Types
import Velo.Terms
import Velo.Values
import Velo.Semantics.Evaluation

import Velo.Core

export
eval : {type : Ty}
    -> (this : Term Nil type)
            -> Velo (Result this)
eval this
  = maybe (throw (Eval OOF))
          (pure)
          (eval this)


-- [ EOF ]
