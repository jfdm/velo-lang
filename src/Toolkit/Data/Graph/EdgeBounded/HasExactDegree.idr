|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Graph.EdgeBounded.HasExactDegree

import Decidable.Equality

import Data.String
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Decidable.Do
import Toolkit.Decidable.Informative

import Toolkit.Data.Nat
import Toolkit.Data.Pair
import Toolkit.Data.List.Size
import Toolkit.Data.List.Occurs.Does

import Toolkit.Data.Graph.EdgeBounded

import public Toolkit.Data.Graph.EdgeBounded.DegreeCommon

%default total

namespace Out

  public export
  HasExactDegreeOut : (v  : Nat)
                   -> (es : Edges)
                   -> (d  : Nat)
                         -> Type
  HasExactDegreeOut v
    = Exactly.Occurs (Pair Nat Nat) (IsFirst v)


  export
  hasExactDegreeOut : (v  : Nat)
                   -> (es : Edges)
                   -> (d  : Nat)
                         -> DecInfo HasDegree.Error
                                    (HasExactDegreeOut v es d)

  hasExactDegreeOut v es d
    = embed (MkError v O)
            (Exactly.occurs (isFirst v) es d)

namespace In

  public export
  HasExactDegreeIn : (v  : Nat)
                  -> (es : Edges)
                  -> (d  : Nat)
                        -> Type
  HasExactDegreeIn v
    = Exactly.Occurs (Pair Nat Nat) (IsSecond v)

  export
  hasExactDegreeIn : (v  : Nat)
                  -> (es : Edges)
                  -> (d  : Nat)
                        -> DecInfo HasDegree.Error
                                   (HasExactDegreeIn v es d)
  hasExactDegreeIn v es d
    = embed (MkError v I)
            (Exactly.occurs (isSecond v) es d)


namespace Error
  public export
  data Kind = WrongIN
            | WrongOUT
            | WrongLeafSrcIN
            | WrongLeafSrcOUT
            | WrongLeafSnkIN
            | WrongLeafSnkOUT

public export
record Error type where
  constructor MkError
  vertex : Vertex type
  kind   : Error.Kind
  error  : HasDegree.Error

namespace Raw

  public export
  data ExpDegrees : (v : Vertex type) -> (i,o : Nat) -> Type where
    Node : ExpDegrees (Node d     k j i) j i
    Src  : ExpDegrees (Leaf d SRC k j)   0 j
    Bsrc : ExpDegrees (Leaf d BI  k j)   0 j
    Snk  : ExpDegrees (Leaf d SNK k j)   j 0
    Bsnk : ExpDegrees (Leaf d BI  k j)   j 0

  public export
  data HasExactDegree : (v   : Vertex type)
                     -> (es  : Edges)
                     -> (i,o : Nat)
                     -> (exp : ExpDegrees v i o)
                            -> Type
    where
      HDN : (din  : HasExactDegreeIn  v es i)
         -> (dout : HasExactDegreeOut v es o)
                 -> HasExactDegree (Node d v i o) es i o Node

      HDLS : (din  : HasExactDegreeIn  v es 0)
          -> (dout : HasExactDegreeOut v es o)
                  -> HasExactDegree (Leaf d SRC v o) es 0 o Src

      HDLT : (din  : HasExactDegreeIn  v es i)
          -> (dout : HasExactDegreeOut v es 0)
                  -> HasExactDegree (Leaf d SNK v i) es i 0 Snk

      HDLBS : (din  : HasExactDegreeIn  v es 0)
           -> (dout : HasExactDegreeOut v es k)
                   -> HasExactDegree (Leaf d BI v k) es 0 k Bsrc

      HDLBT : (din  : HasExactDegreeIn  v es k)
           -> (dout : HasExactDegreeOut v es 0)
                   -> HasExactDegree (Leaf d BI v k) es k 0 Bsnk



  leafBiAsSrcOutWrong : (HasExactDegreeOut       k    es   o      -> Void)
                      -> HasExactDegree (Leaf d BI k o) es 0 o Bsrc -> Void
  leafBiAsSrcOutWrong f (HDLBS din dout) = f dout

  leafBiAsSrcInWrong : (HasExactDegreeIn        k    es 0        -> Void)
                    ->  HasExactDegree (Leaf d BI k o) es 0 o Bsrc -> Void
  leafBiAsSrcInWrong f (HDLBS din dout) = f din

  leafBiAsSnkOutWrong : (HasExactDegreeOut       k    es   0      -> Void)
                     ->  HasExactDegree (Leaf d BI k o) es o 0 Bsnk -> Void
  leafBiAsSnkOutWrong f (HDLBT din dout) = f dout

  leafBiAsSnkInWrong : (HasExactDegreeIn        k    es o        -> Void)
                    ->  HasExactDegree (Leaf d BI k o) es o 0 Bsnk -> Void
  leafBiAsSnkInWrong f (HDLBT din dout) = f din

  export
  hasExactDegree : (v   : Vertex type)
           -> (exp : ExpDegrees v i o)
           -> (es  : Edges)
                  -> DecInfo (HasExactDegree.Error type)
                             (HasExactDegree v es i o exp)

  hasExactDegree (Node d k i o) Node es with (hasExactDegreeIn k es i)
    hasExactDegree (Node d k i o) Node es | (Yes pI) with (hasExactDegreeOut k es o)
      hasExactDegree (Node d k i o) Node es | (Yes pI) | (Yes pO)
        = Yes (HDN pI pO)
      hasExactDegree (Node d k i o) Node es | (Yes pI) | (No msg contra)
        = No (MkError (Node d k i o) WrongOUT msg)
             (\(HDN pI pO) => contra pO)

    hasExactDegree (Node d k i o) Node es | (No msg contra)
      = No (MkError (Node d k i o) WrongIN msg)
           (\(HDN pI pO) => contra pI)

  hasExactDegree (Leaf d SRC k o) Src es with (hasExactDegreeIn k es 0)
    hasExactDegree (Leaf d SRC k o) Src es | (Yes pI) with (hasExactDegreeOut k es o)
      hasExactDegree (Leaf d SRC k o) Src es | (Yes pI) | (Yes pO)
        = Yes (HDLS pI pO)
      hasExactDegree (Leaf d SRC k o) Src es | (Yes pI) | (No msg contra)
        = No (MkError (Leaf d SRC k o) WrongOUT msg)
             (\(HDLS pI pO) => contra pO)

    hasExactDegree (Leaf d SRC k o) Src es | (No msg contra)
      = No (MkError (Leaf d SRC k o) WrongIN msg)
           (\(HDLS pI pO) => contra pI)

  hasExactDegree (Leaf d BI k o) Bsrc es with (hasExactDegreeIn k es 0)
    hasExactDegree (Leaf d BI k o) Bsrc es | (Yes pI) with (hasExactDegreeOut k es o)
      hasExactDegree (Leaf d BI k o) Bsrc es | (Yes pI) | (Yes pO)
        = Yes (HDLBS pI pO)
      hasExactDegree (Leaf d BI k o) Bsrc es | (Yes pI) | (No msg contra)
        = No (MkError (Leaf d BI k o) WrongLeafSrcOUT msg)
             (leafBiAsSrcOutWrong contra)

    hasExactDegree (Leaf d BI k o) Bsrc es | (No msg contra)
      = No (MkError (Leaf d BI k o) WrongLeafSrcIN msg)
           (leafBiAsSrcInWrong contra)

  hasExactDegree (Leaf d SNK k i) Snk es with (hasExactDegreeIn k es i)
    hasExactDegree (Leaf d SNK k i) Snk es | (Yes pI) with (hasExactDegreeOut k es 0)
      hasExactDegree (Leaf d SNK k i) Snk es | (Yes pI) | (Yes pO)
        = Yes (HDLT pI pO)
      hasExactDegree (Leaf d SNK k i) Snk es | (Yes pI) | (No msg contra)
        = No (MkError (Leaf d SNK k i) WrongLeafSnkOUT msg)
             (\(HDLT pI pO) => contra pO)

    hasExactDegree (Leaf d SNK k i) Snk es | (No msg contra)
      = No (MkError (Leaf d SNK k i) WrongLeafSnkIN msg)
           (\(HDLT pI pO) => contra pI)

  hasExactDegree (Leaf d BI k i) Bsnk es with (hasExactDegreeIn k es i)
    hasExactDegree (Leaf d BI k i) Bsnk es | (Yes pO) with (hasExactDegreeOut k es 0)
      hasExactDegree (Leaf d BI k i) Bsnk es | (Yes pO) | (Yes pI)
        = Yes (HDLBT pO pI)
      hasExactDegree (Leaf d BI k i) Bsnk es | (Yes pO) | (No msg contra)
        = No (MkError (Leaf d SNK k i) WrongLeafSnkOUT msg)
             (leafBiAsSnkOutWrong contra)

    hasExactDegree (Leaf d BI k i) Bsnk es | (No msg contra)
      = No (MkError (Leaf d SNK k i) WrongLeafSnkIN msg)
           (leafBiAsSnkInWrong contra)


public export
data HasExactDegree : (v : Vertex type) -> (es : Edges) -> Type where
  R : (exp : ExpDegrees v i o)
   -> (prf : HasExactDegree v es i o exp)
          -> HasExactDegree v es


biLeafWrong : (HasExactDegree (Leaf d BI k j) es j 0 Bsnk -> Void)
           -> (HasExactDegree (Leaf d BI k j) es 0 j Bsrc -> Void)
           ->  HasExactDegree (Leaf d BI k j) es          -> Void
biLeafWrong f g (R Bsrc prf) = g prf
biLeafWrong f g (R Bsnk prf) = f prf

export
hasExactDegree : (v  : Vertex type)
              -> (es : Edges)
                    -> DecInfo (HasExactDegree.Error type)
                               (HasExactDegree v es)

hasExactDegree (Node d k j i) es with (hasExactDegree (Node d k j i) Node es)
  hasExactDegree (Node d k j i) es | (Yes prf)
    = Yes (R Node prf)
  hasExactDegree (Node d k j i) es | (No msg contra)
    = No msg
         (\(R Node prf) => contra prf)

hasExactDegree (Leaf d SRC k j) es with (hasExactDegree (Leaf d SRC k j) Src es)
  hasExactDegree (Leaf d SRC k j) es | (Yes prf)
    = Yes (R Src prf)
  hasExactDegree (Leaf d SRC k j) es | (No msg contra)
    = No msg
         (\(R Src prf) => contra prf)

hasExactDegree (Leaf d SNK k j) es with (hasExactDegree (Leaf d SNK k j) Snk es)
  hasExactDegree (Leaf d SNK k j) es | (Yes prf)
    = Yes (R Snk prf)
  hasExactDegree (Leaf d SNK k j) es | (No msg contra)
    = No msg (\(R Snk prf) => contra prf)

hasExactDegree (Leaf d BI k j) es with (hasExactDegree (Leaf d BI k j) Bsrc es)
  hasExactDegree (Leaf d BI k j) es | (Yes prf)
    = Yes (R Bsrc prf)

  hasExactDegree (Leaf d BI k j) es | (No msgi contra) with (hasExactDegree (Leaf d BI k j) Bsnk es)
    hasExactDegree (Leaf d BI k j) es | (No msgi contra) | (Yes prf)
      = Yes (R Bsnk prf)

    hasExactDegree (Leaf d BI k j) es | (No msgi contra) | (No msg f)
      = No msg (biLeafWrong f contra)

-- [ EOF ]
