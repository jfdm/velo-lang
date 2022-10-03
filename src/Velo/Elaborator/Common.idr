module Velo.Elaborator.Common

import Decidable.Equality

import Velo.Core
import Velo.Error
import Velo.Types

import Toolkit.Decidable.Informative

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

export
dec : FileContext
   -> Elaborating.Error
   -> Dec     a
   -> Velo a
dec _ _ (Yes prf)
  = pure prf
dec fc err (No _)
  = throwAt fc err

export
decInfo : FileContext
       -> Elaborating.Error
       -> DecInfo e a
       -> Velo   a
decInfo _ _ (Yes prf)
  = pure prf
decInfo fc e (No msg prf)
  = throwAt fc e
