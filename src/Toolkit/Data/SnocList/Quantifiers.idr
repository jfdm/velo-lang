module Toolkit.Data.SnocList.Quantifiers

import Data.List.Quantifiers
import public Data.SnocList.Quantifiers

%default total

export
(<>>) : All p sx -> All p xs -> All p (sx <>> xs)
[<] <>> pxs = pxs
(psx :< px) <>> pxs = psx <>> (px :: pxs)

export
(<><) : All p sx -> All p xs -> All p (sx <>< xs)
psx <>< [] = psx
psx <>< (px :: pxs) = (psx :< px) <>< pxs

export
unzipWith : (a -> (x : b ** p x)) ->
            List a ->
            (xs : SnocList b ** All p xs)
unzipWith f = go ([<] ** [<]) where

  go : (xs : SnocList b ** All p xs) ->
       List a ->
       (xs : SnocList b ** All p xs)
  go acc [] = acc
  go (ys ** pys) (x :: xs) =
    let (y ** py) = f x in
    go (ys :< y ** pys :< py) xs
