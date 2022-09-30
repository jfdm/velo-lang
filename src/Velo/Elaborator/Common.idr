module Velo.Elaborator.Common

import Decidable.Equality

import Velo.Core
import Velo.Types

%default total

export
compare : (fc  : FileContext)
       -> (a,b : Ty)
       -> Velo (a = b)
compare fc a b
  = dec fc (Mismatch a b)
           (decEq    a b)
