|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Decidable.Equality.Indexed

import public Decidable.Equality

%default total

public export
data Equals : (t : Type)
           -> (e : t -> Type)
           -> {i,j : t}
           -> (x : e i)
           -> (y : e j)
                -> Type
  where
    Same : {  i,j : t}
        -> {  x      : e i}
        -> {  y      : e j}
        -> (  prfIdx : i = j)
        -> (  prfVal : x = y)
                   -> Equals t e x y

public export
interface DecEq iTy
       => DecEqIdx (iTy : Type)
                   (eTy : iTy -> Type) | eTy
  where
     decEq : {i,j : iTy}
          -> (x : eTy i)
          -> (y : eTy j)
          -> (prf : i = j)
          -> Dec (Equals iTy eTy x y)

export
sym : {i,j : iTy}
   -> {a : eTy i}
   -> {b : eTy j}
   -> (rule : Equals iTy eTy a b) -> Equals iTy eTy b a
sym (Same Refl Refl) = Same Refl Refl

export
negEqSym : {i,j : iTy}
        -> {a : eTy i}
        -> {b : eTy j}
        -> (Equals iTy eTy a b -> Void)
        -> (Equals iTy eTy b a -> Void)
negEqSym p h = p (sym h)

export
trans : {i,j,k : iTy}
     -> {a : eTy i}
     -> {b : eTy j}
     -> {c : eTy k}
     -> (ab : Equals iTy eTy a b)
     -> (bc : Equals iTy eTy b c)
           -> Equals iTy eTy a c
trans {i = i} {j = i} {k = k} {a = a} {b = a} {c = c} (Same Refl Refl) bc with (bc)
  trans {i = i} {j = i} {k = i} {a = a} {b = a} {c = a} (Same Refl Refl) bc | (Same Refl Refl) = (Same Refl Refl)

namespace Index
  public export
  indexAreSame : {i,j : iTy}
              -> (contra : i = j -> Void)
              -> {x : eTy i}
              -> {y : eTy j}
              -> (prf    : Equals iTy eTy x y)
                        -> Void
  indexAreSame contra (Same Refl prfVal) = contra Refl

  public export
  decEq : {iTy : Type}
       -> {eTy : iTy -> Type}
       -> DecEqIdx iTy eTy
       => {i : iTy}
       -> {j : iTy}
       -> (x : eTy i)
       -> (y : eTy j)
       -> Dec (Equals iTy eTy x y)
  decEq x y {i} {j} {eTy} with (decEq i j)
    decEq x y {i = i} {j = i} {eTy = eTy} | (Yes Refl) = Indexed.decEq x y Refl
    decEq x y {i = i} {j = j} {eTy = eTy} | (No contra) = No (indexAreSame contra)

public export
same : Equals kind type x y -> x = y
same (Same Refl Refl) = Refl

-- --------------------------------------------------------------------- [ EOF ]
