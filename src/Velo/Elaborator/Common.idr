module Velo.Elaborator.Common

import Decidable.Equality

import Velo.Core
import Velo.Error
import Velo.Types

%default total

export
compare : (fc  : FileContext)
       -> (a,b : Ty)
       -> Velo (a = b)
compare fc a b
  = dec fc (Mismatch a b)
           (decEq    a b)

export
isTyFunc : (fc : FileContext) -> (ty : Ty) -> Velo (IsTyFunc ty)
isTyFunc fc ty = case isTyFunc ty of
  Just prf => pure prf
  Nothing => throwAt fc (FuncExpected ty)
