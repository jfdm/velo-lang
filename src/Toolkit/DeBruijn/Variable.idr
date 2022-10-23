||| Naming
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Variable

import Decidable.Equality
import Data.SnocList

import Toolkit.Decidable.Informative

import Toolkit.Data.SnocList.AtIndex
import Toolkit.Data.SnocList.Thinning

%default total

public export
data IsVar : (ctxt : SnocList kind)
          -> (type :      kind)
                  -> Type
  where
    V : (  pos : Nat)
     -> (0 prf : AtIndex type ctxt pos)
              -> IsVar   ctxt type

export
Uninhabited (IsVar [<] x) where
  uninhabited (V n prf) = void (uninhabited prf)

export
DecEq (IsVar ctxt type) where
  decEq (V m p) (V n q) with (decEq m n)
    decEq (V .(m) p) (V m q) | Yes Refl
      = Yes (rewrite irrelevantAtIndex p q in Refl)
    _ | No neq = No (\case Refl => neq Refl)

public export
%inline
here : IsVar (ctxt :< a) a
here = V 0 Here

public export
%inline
shift : IsVar ctxt type -> IsVar (ctxt :< a) type
shift (V pos prf) = V (S pos) (There prf)

export
shifts : IsVar g s -> {g' : SnocList a} -> IsVar (g <+> g') s
shifts v {g' = [<]} = v
shifts v {g' = _ :< _} = shift (shifts v)

public export
data View : IsVar ctxt type -> Type where
  Here : View Variable.here
  There : (v : IsVar ctxt type) -> View (shift v)

export
view : (v : IsVar ctxt type) -> View v
view (V 0 Here) = Here
view (V (S n) (There prf)) = There (V n prf)

public export
%inline
weaken : (func : IsVar old type
              -> IsVar new type)
      -> (IsVar (old :< type') type
       -> IsVar (new :< type') type)
weaken f v@_ with (view v)
  _ | Here = here
  _ | There later = shift (f later)

export
thin : IsVar g s -> Thinning g g' -> IsVar g' s
thin v Empty = absurd v
thin v (Skip th) = shift (thin v th)
thin v@_ (Keep Refl th) with (view v)
  _ | Here = here
  _ | There w = shift (thin w th)

-- [ EOF ]
