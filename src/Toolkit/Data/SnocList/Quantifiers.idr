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
