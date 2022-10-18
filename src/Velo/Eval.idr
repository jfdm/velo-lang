module Velo.Eval

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term
import Velo.Values
import Velo.Semantics.Evaluation

import Velo.Core

export
eval : {type : Ty}
    -> (this : Term metas [<] type)
            -> Velo (Result this)
eval this
  = maybe (throw (Eval OOF))
          (pure)
          (eval this)


-- [ EOF ]
