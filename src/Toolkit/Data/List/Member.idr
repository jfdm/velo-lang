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
hereNotShift : Not (Member.here === Member.shift v)
hereNotShift {v = V n prf} Refl impossible

export
shiftNotHere : Not (Member.shift v === Member.here)
shiftNotHere {v = V n prf} Refl impossible

export
shiftInjective : shift v === shift w -> v === w
shiftInjective {v = V m p} {w = V m p} Refl = Refl

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

export
lookup : {ctxt : _} -> IsMember ctxt ty -> (ty' : _ ** ty === ty')
lookup v = case view v of
  Here => (_ ** Refl)
  There v => lookup v

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

public export
decEqHet : (v : IsMember tys ty1) ->
           (w : IsMember tys ty2) ->
           Dec (ty1 === ty2, v ~=~ w)
decEqHet v@_ w@_ with (view v) | (view w)
  _ | Here | Here = Yes (Refl, Refl)
  _ | There v' | Here = No (\ (Refl, p) => shiftNotHere p)
  _ | Here | There w' = No (\ (Refl, p) => hereNotShift p)
  _ | There v' | There w' with (decEqHet v' w')
    _ | Yes (Refl, eq2) = Yes (Refl, cong shift eq2)
    _ | No neq = No (\ (Refl, eq) => neq (Refl, shiftInjective eq))

-- [ EOF ]
