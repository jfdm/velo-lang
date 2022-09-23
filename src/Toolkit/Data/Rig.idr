|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Rig

import public Decidable.Equality
import public Data.Vect

%default total

public export
data TyRig = None | One | Tonne

public export
noneNotOne : (None = One) -> Void
noneNotOne Refl impossible

public export
noneNotTonne : (None = Tonne) -> Void
noneNotTonne Refl impossible

public export
oneNotTonne : (One = Tonne) -> Void
oneNotTonne Refl impossible

public export
DecEq TyRig where
  decEq None None = Yes Refl
  decEq None One = No noneNotOne
  decEq None Tonne = No noneNotTonne
  decEq One None = No (negEqSym noneNotOne)
  decEq One One = Yes Refl
  decEq One Tonne = No oneNotTonne
  decEq Tonne None = No (negEqSym noneNotTonne)
  decEq Tonne One = No (negEqSym oneNotTonne)
  decEq Tonne Tonne = Yes Refl


public export
plus : TyRig -> TyRig -> TyRig
plus None None = None
plus None One = One
plus None Tonne = Tonne
plus One None = One
plus One One = Tonne
plus One Tonne = Tonne
plus Tonne None = Tonne
plus Tonne One = Tonne
plus Tonne Tonne = Tonne

public export
multiply : TyRig -> TyRig -> TyRig
multiply None None = None
multiply None One = None
multiply None Tonne = None
multiply One None = None
multiply One One = One
multiply One Tonne = Tonne
multiply Tonne None = None
multiply Tonne One = Tonne
multiply Tonne Tonne = Tonne

public export
product : Vect n TyRig -> Vect n TyRig -> Vect n TyRig
product [] [] = []
product (x :: xs) (y :: ys) = multiply x y :: product xs ys

public export
sum : Vect n TyRig -> Vect n TyRig -> Vect n TyRig
sum [] [] = []
sum (x :: xs) (y :: ys) = plus x y :: sum xs ys
