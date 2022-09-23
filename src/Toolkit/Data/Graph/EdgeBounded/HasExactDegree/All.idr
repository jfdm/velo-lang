|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Graph.EdgeBounded.HasExactDegree.All

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
import public Toolkit.Data.Graph.EdgeBounded.HasExactDegree

%default total

public export
HasExactDegrees : Vertices type -> Edges -> Type
HasExactDegrees vs es = All (\v => HasExactDegree v es) vs

errorHead : {x : type}
         -> {p : type -> Type}
         -> (p x -> Void)
         -> All p (x :: xs) -> Void
errorHead contra (y :: z) = contra y

errorTail : (All p xs -> Void) -> All p (x :: xs) -> Void
errorTail f (y :: z) = f z

all : {type : Type}
   -> {p  : type -> Type}
   -> (f  : (x : type) -> DecInfo e (p x))
   -> (xs : List type)
         -> DecInfo e (All p xs)
all f [] = Yes []
all f (x :: xs) with (f x)
  all f (x :: xs) | (Yes prfWhy) with (all f xs)
    all f (x :: xs) | (Yes prfWhy) | (Yes y)
      = Yes (prfWhy :: y)
    all f (x :: xs) | (Yes prfWhy) | (No msgWhyNot prfWhyNot)
      = No msgWhyNot (errorTail prfWhyNot)

  all f (x :: xs) | (No msgWhyNot prfWhyNot) = No msgWhyNot (errorHead prfWhyNot)

export
hasExactDegrees : {type : Type}
               -> (vs   : Vertices type)
               -> (es   : Edges)
                       -> DecInfo (HasExactDegree.Error type)
                                  (HasExactDegrees vs es)
hasExactDegrees vs es = all (\v => hasExactDegree v es) vs

-- [ EOF ]
