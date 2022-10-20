module Velo.Eval

import public Toolkit.DeBruijn.Evaluation

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term
import Velo.Values

import public Velo.Semantics.Reductions
import Velo.Semantics.Progress

import Velo.Core

export
eval : {type : Ty}
    -> (this : Term metas [<] type)
            -> Velo (Result Ty (Term metas) Value Redux this)
eval this
  = maybe (throw (Eval OOF))
          (pure)
          (eval this)


-- [ EOF ]
