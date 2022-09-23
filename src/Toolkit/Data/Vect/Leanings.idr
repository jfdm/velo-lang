|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Vect.Leanings

import Data.Vect

import Toolkit.Data.DVect

namespace Index
  public export
  data Leans : (o,l,c,r : Nat) -> Type where
    Empty : Leans Z Z Z Z

    Left : Leans    os     ls  cs rs
        -> Leans (S os) (S ls) cs rs

    Center : Leans    os  ls    cs  rs
          -> Leans (S os) ls (S cs) rs

    Right : Leans    os  ls cs    rs
         -> Leans (S os) ls cs (S rs)

public export
data IsCenter : (type    : Type)
             -> (goLeft  : type -> Type)
             -> (goRight : type -> Type)
             -> (o       : type)
                        -> Type
  where
    C : (noLeft  : left  o -> Void)
     -> (noRight : right o -> Void)
                -> IsCenter type left right o

public export
data Leaning : (type    : Type)
            -> (goLeft  : type -> Type)
            -> (goRight : type -> Type)
            -> (idx     : Leans o l c r)
            -> (os      : Vect  o        type)
            -> (ls      : Vect    l      type)
            -> (cs      : Vect      c    type)
            -> (rs      : Vect        r  type)
                       -> Type
  where
    Empty : Leaning type left right Empty Nil Nil Nil Nil

    Left : {o : type}
        -> (prf  : left o)
        -> (rest : Leaning type left right       idx      os      ls  cs rs)
                -> Leaning type left right (Left idx) (o::os) (o::ls) cs rs

    Center : {o : type}
          -> (prf  : IsCenter type left right o)
          -> (rest : Leaning  type left right         idx      os  ls     cs  rs)
                  -> Leaning  type left right (Center idx) (o::os) ls (o::cs) rs

    Right : {o : type}
         -> (prf  : right o)
         -> (rest : Leaning type left right        idx      os  ls cs     rs)
                 -> Leaning type left right (Right idx) (o::os) ls cs (o::rs)

public export
data Result : (type    : Type)
           -> (isLeft  : (o : type) -> Type)
           -> (isRight : (o : type) -> Type)
           -> (os      : Vect o type)
                      -> Type
  where
    R : (lefts   : Vect l type)
     -> (centers : Vect c type)
     -> (rights  : Vect r type)
     -> (idx     : Leans o l c r)

     -> (leaning   : Leaning type isLeft isRight idx os lefts centers rights)
     -> (prfLeft   : DVect type isLeft l lefts)
     -> (prfCenter : DVect type (IsCenter type isLeft isRight) c centers)
     -> (prfRight  : DVect type isRight r rights)
                  -> Result type isLeft isRight os

export
leans : {type  : Type}
     -> {left  : type -> Type}
     -> {right : type -> Type}
     -> (isLeft  : (o : type) -> Dec (left  o))
     -> (isRight : (o : type) -> Dec (right o))
     -> (os      : Vect o type)
                -> Result type left right os
leans isLeft isRight []
  = R [] [] [] Empty Empty [] [] []

leans l r (x :: xs) with (l x)
  leans l r (x :: xs) | (Yes prf) with (leans l r xs)
    leans l r (x :: xs) | (Yes prf) | (R lefts centers rights idx lean prfLeft prfCenter prfRight)
      = R (x::lefts) centers rights (Left idx) (Left prf lean) (prf :: prfLeft) prfCenter prfRight

  leans l r (x :: xs) | (No noL) with (r x)
    leans l r (x :: xs) | (No noL) | (Yes prf) with (leans l r xs)
      leans l r (x :: xs) | (No noL) | (Yes prf) | (R ls cs rs idx lean pLs pCs pRs)
        = R ls cs (x::rs) (Right idx) (Right prf lean) pLs pCs (prf :: pRs)

    leans l r (x :: xs) | (No noL) | (No noR) with (leans l r xs)
      leans l r (x :: xs) | (No noL) | (No noR) | (R ls cs rs idx lean pLs pCs pRs)
        = R ls (x::cs) rs (Center idx) (Center (C noL noR) lean) pLs (C noL noR :: pCs) pRs

namespace Poll

  public export
  data LeansLeft : (poll : Leaning type l r i os ls rs cs)
                        -> Type
    where
      EmptyL : LeansLeft Empty

      IsLeft : {rest  : Leaning type l r i os ls cs rs}
            -> {prf   : l o}
            -> (later : LeansLeft           rest)
                     -> LeansLeft (Left prf rest)

  Uninhabited (LeansLeft (Center prf rest)) where
    uninhabited EmptyL impossible
    uninhabited (IsLeft later) impossible

  Uninhabited (LeansLeft (Right prf rest)) where
    uninhabited EmptyL impossible
    uninhabited (IsLeft later) impossible

  export
  leansLeft : (poll : Leaning type l r i os ls cs rs)
                   -> Dec (LeansLeft poll)
  leansLeft Empty
    = Yes EmptyL

  leansLeft (Left prf rest) with (leansLeft rest)
    leansLeft (Left prf rest) | (Yes x)
      = Yes (IsLeft x)

    leansLeft (Left prf rest) | (No contra)
      = No (\(IsLeft later) => contra later)

  leansLeft (Center prf rest)
    = No absurd

  leansLeft (Right prf rest)
    = No absurd

  public export
  data LeansRight : (poll : Leaning type l r i os ls cs rs)
                        -> Type
    where
      EmptyR : LeansRight Empty

      IsRight : {rest  : Leaning type l r i os ls cs rs}
             -> {prf   : r o}
             -> (later : LeansRight rest)
                      -> LeansRight (Right prf rest)

  Uninhabited (LeansRight (Center prf rest)) where
    uninhabited EmptyR impossible
    uninhabited (IsRight later) impossible

  Uninhabited (LeansRight (Left prf rest)) where
    uninhabited EmptyR impossible
    uninhabited (IsRight later) impossible

  export
  leansRight : (poll : Leaning type l r i os ls cs rs)
                    -> Dec (LeansRight poll)
  leansRight Empty
    = Yes EmptyR

  leansRight (Right prf rest) with (leansRight rest)
    leansRight (Right prf rest) | (Yes x)
      = Yes (IsRight x)

    leansRight (Right prf rest) | (No contra)
      = No (\(IsRight later) => contra later)

  leansRight (Center prf rest)
    = No absurd

  leansRight (Left prf rest)
    = No absurd

  public export
  data LeansCenter : (poll : Leaning type l r i os ls cs rs)
                        -> Type
    where
      EmptyC : LeansCenter Empty

      IsCenter : {rest  : Leaning type l r i os ls cs rs}
              -> {prf   : IsCenter type l r o}
              -> (later : LeansCenter rest)
                       -> LeansCenter (Center prf rest)

  Uninhabited (LeansCenter (Right prf rest)) where
    uninhabited EmptyC impossible
    uninhabited (IsCenter later) impossible

  Uninhabited (LeansCenter (Left prf rest)) where
    uninhabited EmptyC impossible
    uninhabited (IsCenter later) impossible

  export
  leansCenter : (poll : Leaning type l r i os ls cs rs)
                     -> Dec (LeansCenter poll)
  leansCenter Empty
    = Yes EmptyC

  leansCenter (Center prf rest) with (leansCenter rest)
    leansCenter (Center prf rest) | (Yes x)
      = Yes (IsCenter x)

    leansCenter (Center prf rest) | (No contra)
      = No (\(IsCenter later) => contra later)

  leansCenter (Right prf rest)
    = No absurd

  leansCenter (Left prf rest)
    = No absurd

public export
data HowLeans : (poll : Leaning type l r i os ls cs rs) -> Type where
  LE : HowLeans Empty
  LL : LeansLeft poll -> HowLeans poll

  LC : (LeansLeft  poll -> Void)
    -> (LeansRight poll -> Void)
    -> HowLeans poll

  LR : LeansRight poll -> HowLeans poll

export
howLeans : (poll : Leaning type l r i os ls cs rs) -> HowLeans poll
howLeans {ls=Nil} {cs=Nil} {rs=Nil} Empty = LE

howLeans {ls} {cs} {rs} poll with (leansLeft poll)
  howLeans {ls = ls} {cs = cs} {rs = rs} poll | (Yes prf)
    = LL prf

  howLeans {ls = ls} {cs = cs} {rs = rs} poll | (No noL) with (leansRight poll)
    howLeans {ls = ls} {cs = cs} {rs = rs} poll | (No noL) | (Yes prf)
      = LR prf

    howLeans {ls = ls} {cs = cs} {rs = rs} poll | (No noL) | (No noR)
      = LC noL noR

-- [ EOF ]
