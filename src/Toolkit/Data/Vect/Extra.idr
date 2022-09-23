|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Vect.Extra

import Data.Nat

import public Decidable.Equality
import        Data.Vect
import public Data.Vect.AtIndex

import public Toolkit.Decidable.Informative

%default total

namespace Equality
   public export
   vecEq : Eq type => Vect n type -> Vect m type -> Bool
   vecEq [] [] = True
   vecEq [] (x :: xs) = False
   vecEq (x :: xs) [] = False
   vecEq (x :: xs) (y :: ys) = x == y && vecEq xs ys

namespace Decidable
  namespace SameLength
    public export
    decEq : DecEq type
          => (n = m)
          -> (xs : Vect n type)
          -> (ys : Vect m type)
          -> Dec (xs = ys)
    decEq Refl xs ys with (decEq xs ys)
      decEq Refl ys ys | (Yes Refl) = Yes Refl
      decEq Refl xs ys | (No contra) = No contra

  namespace DiffLength

    public export
    vectorsDiffLength : DecEq type
                      => (contra : (n = m) -> Void)
                      -> {xs : Vect n type}
                      -> {ys : Vect m type}
                      -> (xs = ys) -> Void
    vectorsDiffLength contra Refl = contra Refl

    public export
    decEq : DecEq type
         => {n,m : Nat}
         -> (xs : Vect n type)
         -> (ys : Vect m type)
         -> Dec (xs = ys)
    decEq xs ys {n} {m} with (decEq n m)
      decEq xs ys {n = m} {m = m} | (Yes Refl) = decEq Refl xs ys
      decEq xs ys {n = n} {m = m} | (No contra) = No (vectorsDiffLength contra)

namespace Shape

  public export
  data Shape : (xs : Vect n a)
            -> (ys : Vect m a)
            -> Type
    where
      Empty : Shape Nil Nil
      LH    : Shape (x::xs) Nil
      RH    : Shape Nil      (y::ys)
      Both  : Shape (x::xs) (y::ys)

  export
  shape : (xs : Vect n a)
       -> (ys : Vect m a)
       -> Shape xs ys
  shape [] [] = Empty
  shape [] (y :: ys) = RH
  shape (x :: xs) [] = LH
  shape (x :: xs) (y :: ys) = Both

namespace ReplaceAt

  public export
  data ReplaceAt : (idx       : Fin n)
                -> (xs        : Vect n a)
                -> (this,that : a)
                -> (ys        : Vect n a)
                             -> Type
    where
      H : ReplaceAt FZ (x::xs)
                        x
                        y
                       (y::xs)

      T : ReplaceAt     idx       xs  x y      ys
       -> ReplaceAt (FS idx) (x'::xs) x y (x'::ys)

  notSame : (x = this -> Void) -> DPair (Vect (S len) a) (ReplaceAt FZ (x :: xs) this that) -> Void
  notSame _ (MkDPair _ (T y)) impossible

  notLater : (DPair (Vect len a) (ReplaceAt x xs this that) -> Void) -> DPair (Vect (S len) a) (ReplaceAt (FS x) (y :: xs) this that) -> Void
  notLater f (MkDPair (y :: ys) (T z)) = f (MkDPair ys z)

  export
  replaceAt : DecEq a
           => (idx : Fin n)
           -> (xs  : Vect n a)
           -> (this, that : a)
           -> Dec (DPair (Vect n a) (ReplaceAt idx xs this that))
  replaceAt FZ (x :: xs) this that with (decEq x this)
    replaceAt FZ (x :: xs) x    that | (Yes Refl) = Yes (MkDPair (that :: xs) H)
    replaceAt FZ (x :: xs) this that | (No contra)
      = No (notSame contra)
  replaceAt (FS x) (y :: xs) this that with (replaceAt x xs this that)
    replaceAt (FS x) (y :: xs) this that | (Yes (MkDPair fst snd))
      = Yes (MkDPair (y :: fst) (T snd))
    replaceAt (FS x) (y :: xs) this that | (No contra)
      = No (notLater contra)

namespace Diff

  public export
  data AtIndex : (idx : Fin  m)
              -> (xs  : Vect n type)
              -> (x   : type)
                     -> Type
    where
      I : {idx : Fin n}
       -> {xs  : Vect n type}
       -> (prf : AtIndex.AtIndex idx xs x)
              -> Diff.AtIndex idx xs x

  public export
  index : DecEq type
       => {m,n : Nat}
       -> (idx : Fin m)
       -> (xs  : Vect n type)
              -> Dec (DPair type (Diff.AtIndex idx xs))
  index {m,n} idx xs with (decEq m n)
    index {m=m,n=m} idx xs | (Yes Refl) with (Find.index idx xs)
      index {m=m,n=m} idx xs | (Yes Refl) | (Yes (x ** prf))
        = Yes (x ** I prf)
      index {m=m,n=m} idx xs | (Yes Refl) | (No contra)
        = No (\(MkDPair x (I prf)) => contra (x ** prf))
    index {m,n} idx xs | (No contra)
      = No (\(MkDPair x (I prf)) => contra Refl)

namespace Quantifier
  namespace AtIndex

    public export
    data AtIndex : (type : Type)
                -> (p    : (a : type) -> Type)
                -> (idx  : Fin n)
                -> (xs   : Vect n type)
                        -> Type
      where
        Here : (prf : p x)
                   -> AtIndex type p FZ (x::xs)

        There : (later : AtIndex type p     next            xs)
                      -> AtIndex type p (FS next) (not_x :: xs)

    export
    Uninhabited (AtIndex type p idx Nil) where
      uninhabited (Here prf) impossible
      uninhabited (There later) impossible


    notLater : (AtIndex type p     y        xs  -> Void)
             -> AtIndex type p (FS y) (x :: xs) -> Void
    notLater f (There later) = f later

    notHere : (p x -> Void)
            -> AtIndex type p FZ (x :: xs) -> Void
    notHere f (Here prf) = f prf


    export
    atIndex : {p    : type -> Type}
           -> (dec  : (this : type) -> Dec (p this))
           -> (idx  : Fin n)
           -> (xs   : Vect n type)
                   -> Dec (AtIndex type p idx xs)
    atIndex dec idx []
      = No absurd

    atIndex dec FZ (x :: xs) with (dec x)
      atIndex dec FZ (x :: xs) | (Yes prf)
        = Yes (Here prf)
      atIndex dec FZ (x :: xs) | (No contra)
        = No (notHere contra)


    atIndex dec (FS y) (x :: xs) with (atIndex dec y xs)
      atIndex dec (FS y) (x :: xs) | (Yes prf)
        = Yes (There prf)
      atIndex dec (FS y) (x :: xs) | (No contra)
        = No (notLater contra)

    namespace Diff
      public export
      data AtIndexI : (type : Type)
                   -> (p    : (a : type) -> Type)
                   -> (m,n  : Nat)
                   -> (idx  : Fin m)
                   -> (xs   : Vect n type)
                           -> Type
        where
          At : AtIndex  type p idx xs
            -> AtIndexI type p n n idx xs

      Uninhabited (AtIndexI type p m Z idx Nil) where
        uninhabited (At (Here prf)) impossible
        uninhabited (At (There later)) impossible

      notAtIndex : (AtIndex type p idx xs -> Void)
                -> AtIndexI type p m m idx xs -> Void
      notAtIndex f (At x) = f x

      indexDiffers : (m = n -> Void) -> AtIndexI type p m n idx xs -> Void
      indexDiffers f (At x) = f Refl

      export
      atIndexI : {p    : type -> Type}
              -> {m,n  : Nat}
              -> (dec  : (this : type) -> Dec (p this))
              -> (idx  : Fin m)
              -> (xs   : Vect n type)
                      -> Dec (AtIndexI type p m n idx xs)
      atIndexI {m} {n} dec idx xs with (decEq m n)
        atIndexI {m = m} {n = m} dec idx xs | (Yes Refl) with (atIndex dec idx xs)
          atIndexI {m = m} {n = m} dec idx xs | (Yes Refl) | (Yes prf)
            = Yes (At prf)

          atIndexI {m = m} {n = m} dec idx xs | (Yes Refl) | (No contra)
            = No (notAtIndex contra)
        atIndexI {m = m} {n = n} dec idx xs | (No contra)
          = No (indexDiffers contra)

  namespace Nat
    public export
    data AtIndex : (type : Type)
                -> (p,q  : (a : type) -> Type)
                -> (idx  : Nat)
                -> (xs   : Vect n type)
                        -> Type
      where
        Here : (prf : p x)
                   -> AtIndex type p q Z (x::xs)

        There : (later : AtIndex type p q    next            xs)
                      -> AtIndex type p q (S next) (not_x :: xs)

    public export
    data AtIndexNot : (type : Type)
                   -> (p,q  : (a : type) -> Type)
                   -> (idx  : Nat)
                   -> (xs   : Vect n type)
                           -> Type
       where
         IOOB  : AtIndexNot type p q n xs
         NotSatH : (prf : q x)
                       -> AtIndexNot type p q n (x::xs)
         NotSatT : AtIndexNot type p q    n      xs
                -> AtIndexNot type p q (S n) (x::xs)

    Uninhabited (AtIndex type p q Z Nil) where
      uninhabited (Here _) impossible

    Uninhabited (AtIndex type p q (S n) Nil) where
      uninhabited (Here _) impossible

    export
    atIndex : {p,q  : type -> Type}
           -> (dec  : (this : type) -> DecInfo (q this) (p this))
           -> (idx  : Nat)
           -> (xs   : Vect n type)
                   -> DecInfo (AtIndexNot type p q idx xs)
                              (AtIndex    type p q idx xs)
    atIndex _ Z []
      = No IOOB absurd

    atIndex _ (S k) []
      = No IOOB absurd

    atIndex dec Z (x :: xs) with (dec x)
      atIndex dec Z (x :: xs) | (Yes prf)
        = Yes (Here prf)

      atIndex dec Z (x :: xs) | (No msg no)
        = No (NotSatH msg)
             (\(Here prf) => no prf)

    atIndex dec (S k) (x :: xs) with (atIndex dec k xs)
      atIndex dec (S k) (x :: xs) | (Yes prf)
        = Yes (There prf)
      atIndex dec (S k) (x :: xs) | (No IOOB no)
        = No IOOB
             (\(There later) => no later)
      atIndex dec (S k) (x :: xs) | (No prf no)
        = No (NotSatT prf)
             (\(There later) => no later)

-- [ EOF ]
