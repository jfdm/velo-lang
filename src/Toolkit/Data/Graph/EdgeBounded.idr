||| A graph whose vertices have a restricted in/out degree.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Graph.EdgeBounded

import Decidable.Equality

import Data.String
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Decidable.Do
import Toolkit.Decidable.Informative

import Toolkit.Data.Nat
import Toolkit.Data.Pair
import Toolkit.Data.List.Size
import public Toolkit.Data.List.Occurs.Does

%default total

namespace Vertex
  public export
  data Flow = SRC | SNK | BI

  export
  Show Flow where
    show SRC = "IN"
    show SNK = "OUT"
    show BI = "INOUT"

  Uninhabited (SRC = SNK) where
    uninhabited Refl impossible

  Uninhabited (SRC = BI) where
    uninhabited Refl impossible

  Uninhabited (SNK = BI) where
    uninhabited Refl impossible

  DecEq Flow where
    decEq SRC SRC = Yes Refl
    decEq SRC SNK = No absurd
    decEq SRC BI = No absurd
    decEq SNK SRC = No (negEqSym absurd)
    decEq SNK SNK = Yes Refl
    decEq SNK BI = No absurd
    decEq BI SRC = No (negEqSym absurd)
    decEq BI SNK = No (negEqSym absurd)
    decEq BI BI = Yes Refl


  public export
  data Vertex a = Node a Nat Nat Nat
              | Leaf a Flow Nat Nat


  Uninhabited (Node d k j i = Leaf a s x y) where
    uninhabited Refl impossible

  decEq : DecEq type => (a,b : Vertex type) -> Dec (a = b)
  decEq (Node d k j i) (Node e a b c)
    = decDo $ do Refl <- decEq d e `otherwise` (\Refl => Refl)
                 Refl <- decEq k a `otherwise` (\Refl => Refl)
                 Refl <- decEq j b `otherwise` (\Refl => Refl)
                 Refl <- decEq i c `otherwise` (\Refl => Refl)
                 pure Refl

  decEq (Node _ _ _ _) (Leaf _ _ _ _) = No absurd

  decEq (Leaf _ _ _ _) (Node _ _ _ _) = No (negEqSym absurd)

  decEq (Leaf d k j i) (Leaf e a b c)
    = decDo $ do Refl <- decEq d e `otherwise` (\Refl => Refl)
                 Refl <- decEq k a `otherwise` (\Refl => Refl)
                 Refl <- decEq j b `otherwise` (\Refl => Refl)
                 Refl <- decEq i c `otherwise` (\Refl => Refl)
                 pure Refl

  export
  DecEq type => DecEq (Vertex type ) where
    decEq = Vertex.decEq

  namespace API
    public export
    ident : Vertex type -> Nat
    ident (Node d   k j i) = k
    ident (Leaf d f k j)   = k

    public export
    degreeOut : Vertex type -> Nat
    degreeOut (Node _ k j i)   = i
    degreeOut (Leaf _ SRC k j) = j
    degreeOut (Leaf _ SNK k j) = 0
    degreeOut (Leaf _ BI k j)  = j

    public export
    degreeIn : Vertex type -> Nat
    degreeIn (Node _ k j i)   = j
    degreeIn (Leaf _ SRC k j) = 0
    degreeIn (Leaf _ SNK k j) = j
    degreeIn (Leaf _ BI k j)  = j


    export
    driver : type -> Nat -> Nat -> Vertex type
    driver d = Leaf d SRC

    export
    catcher : type -> Nat -> Nat -> Vertex type
    catcher d = Leaf d SNK

    export
    gateway : type -> Nat -> Nat -> Vertex type
    gateway d = Leaf d BI

    export
    node : type -> Nat -> Nat -> Nat -> Vertex type
    node = Node

    export
    both : type -> Nat -> Nat -> Vertex type
    both d i n = Node d i n n

namespace Graph

  public export
  Vertices : Type -> Type
  Vertices = (List . Vertex)

  public export
  Edge : Type
  Edge = Pair Nat Nat

  public export
  Edges : Type
  Edges = List Edge


  public export
  record Graph type where
    constructor MkGraph
    nodes : Vertices type
    edges : Edges


  public export
  empty : Graph type
  empty = MkGraph Nil Nil



  namespace API

    export
    insertNode : DecEq type => Vertex type -> Graph type -> Graph type
    insertNode k (MkGraph nodes edges) with (isElem k nodes)
      insertNode k (MkGraph nodes edges) | (Yes prf)
        = MkGraph nodes edges
      insertNode k (MkGraph nodes edges) | (No contra)
        = MkGraph (k::nodes) edges


    export
    insertEdge : (Nat, Nat) -> Graph type -> Graph type
    insertEdge (a, b) = { edges $= (::) (a,b)}


    from : DecEq type
        => Graph type
        -> Vertices type
        -> Edges
        -> Graph type
    from g nodes
      = foldr insertEdge (foldr insertNode g nodes)

    export
    fromLists : DecEq type => Vertices type -> Edges -> Graph type
    fromLists = from empty

    export
    updateWith : DecEq type
              => Graph type
              -> Vertices type
              -> Edges
              -> Graph type
    updateWith = from

    export
    merge : DecEq type => (a,b : Graph type) -> Graph type
    merge (MkGraph vs es) g
      = from g vs es


-- [ EOF ]
