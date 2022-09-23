|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.List.View.PairWise

import Data.List

%default total

public export
data PairWise : List a -> Type where
  Empty : PairWise Nil
  One   : (x:a) -> PairWise [x]
  Two   : (x,y : a) -> PairWise [x,y]
  N     : (x,y : a)
       -> PairWise (y::xs)
       -> PairWise (x::y::xs)


export
pairwise : (xs : List a) -> PairWise xs
pairwise [] = Empty
pairwise (x :: []) = One x
pairwise (x :: (y :: xs)) with (pairwise (y::xs))
  pairwise (x :: (y :: [])) | (One y) = Two x y
  pairwise (x :: (y :: [w])) | (Two y w) = N x y (Two y w)
  pairwise (x :: (y :: (w :: xs))) | (N y w v) = N x y (N y w v)

unSafeToList : {xs : List a} -> PairWise xs -> Maybe (List (a,a))
unSafeToList Empty = Just Nil
unSafeToList (One x) = Nothing
unSafeToList (Two x y) = Just [(x,y)]
unSafeToList (N x y z)
  = do rest <- unSafeToList z
       pure (MkPair x y :: rest)

||| Returns a list of pairs if `xs` has even number of elements, Nothing if odd.
export
unSafePairUp : (xs : List a) -> Maybe (List (a,a))
unSafePairUp xs = (unSafeToList (pairwise xs))


-- [ EOF ]
