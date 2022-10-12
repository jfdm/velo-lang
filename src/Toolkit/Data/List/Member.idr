||| Naming
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.Member

import Decidable.Equality

import Toolkit.Decidable.Informative

import Toolkit.Data.List.AtIndex
import Toolkit.Data.List.Thinning

%default total

public export
data IsMember : (ctxt : List kind)
          -> (type :      kind)
                  -> Type
  where
    V : (  pos : Nat)
     -> (0 prf : AtIndex type ctxt pos)
              -> IsMember   ctxt type

export
Uninhabited (IsMember [] x) where
  uninhabited (V n prf) = void (uninhabited prf)

export
DecEq (IsMember ctxt type) where
  decEq (V m p) (V n q) with (decEq m n)
    decEq (V m p) (V .(m) q) | Yes Refl
      = Yes (rewrite irrelevantAtIndex p q in Refl)
    _ | No neq = No (\case Refl => neq Refl)

public export
%inline
here : IsMember (a :: ctxt) a
here = V 0 Here

public export
%inline
shift : IsMember ctxt type -> IsMember (a :: ctxt) type
shift (V pos prf) = V (S pos) (There prf)

export
shifts : IsMember g s -> {g' : List a} -> IsMember (g' <+> g) s
shifts v {g' = []} = v
shifts v {g' = _ :: _} = shift (shifts v)

public export
data View : IsMember ctxt type -> Type where
  Here : View Member.here
  There : (v : IsMember ctxt type) -> View (shift v)

export
view : (v : IsMember ctxt type) -> View v
view (V 0 Here) = Here
view (V (S n) (There prf)) = There (V n prf)

public export
%inline
weaken : (func : IsMember old type
              -> IsMember new type)
      -> (IsMember (type' :: old) type
       -> IsMember (type' :: new) type)
weaken f v@_ with (view v)
  _ | Here = here
  _ | There later = shift (f later)

export
thin : IsMember g s -> Thinning g g' -> IsMember g' s
thin v Empty = absurd v
thin v (Skip th) = shift (thin v th)
thin v@_ (Keep Refl th) with (view v)
  _ | Here = here
  _ | There w = shift (thin w th)

-- [ EOF ]
