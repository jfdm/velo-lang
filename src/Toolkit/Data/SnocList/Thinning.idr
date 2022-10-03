module Toolkit.Data.SnocList.Thinning

import Toolkit.Data.SnocList.Quantifiers
import public Toolkit.Data.SnocList.Subset

public export
Thinning : (sx, sy : SnocList a) -> Type
Thinning = Subset (===)

export
Identity : {sx : SnocList a} -> Thinning sx sx
Identity {sx = [<]} = Empty
Identity {sx = sx :< x} = Keep Refl Identity

namespace All

  export
  Identity : All p sx -> Thinning sx sx
  Identity [<] = Empty
  Identity (psx :< _) = Keep Refl (Identity psx)

infixr 8 <.>
export
(<.>) : Thinning sx sy -> Thinning sy sz -> Thinning sx sz
(<.>) = trans (\ eq1, eq2 => trans eq1 eq2)

namespace Cover

  public export
  data Cover : (th : Thinning {a} sx1 sy) -> (ph : Thinning sx2 sy) -> Type where
    Empty : Cover Empty Empty
    Keep  : Cover th ph -> Cover (Keep Refl th) (Keep Refl ph)
    SkipL : Cover th ph -> Cover (Skip th) (Keep Refl ph)
    SkipR : Cover th ph -> Cover (Keep eq th) (Skip ph)

  export
  coverDec : (th : Thinning {a} sx1 sy) -> (ph : Thinning sx2 sy) -> Dec (Cover th ph)
  coverDec Empty Empty = Yes Empty
  coverDec (Keep Refl th) (Keep Refl ph) with (coverDec th ph)
    _ | Yes p = Yes (Keep p)
    _ | No np = No (\ (Keep p) => void (np p))
  coverDec (Keep eq th) (Skip ph) with (coverDec th ph)
    _ | Yes p = Yes (SkipR p)
    _ | No np = No (\ (SkipR p) => void (np p))
  coverDec (Skip th) (Keep Refl ph) with (coverDec th ph)
    _ | Yes p = Yes (SkipL p)
    _ | No np = No (\ (SkipL p) => void (np p))
  coverDec (Skip th) (Skip ph) = No (\case p impossible)

namespace Join

  public export
  record Join
    {a : Type} {sx1, sx2, sy : SnocList a}
    (th : Thinning sx1 sy)
    (ph : Thinning sx2 sy) where
    constructor MkJoin
    {union : SnocList a}
    {left   : Thinning sx1 union}
    middle : Thinning union sy
    {right  : Thinning sx2 union}
    cover  : Cover left right

  export
  join : {sy : _} -> (th : Thinning sx1 sy) -> (ph : Thinning sx2 sy) -> Join th ph
  join Empty Empty = MkJoin Empty Empty
  join (Keep Refl th) (Keep Refl ph) =
    let (MkJoin middle cover) = join th ph in
    MkJoin (Keep Refl middle) (Keep cover)
  join (Keep Refl th) (Skip ph) =
    let (MkJoin middle cover) = join th ph in
    MkJoin (Keep Refl middle) (SkipR {eq = Refl} cover)
  join (Skip th) (Keep Refl ph) =
    let (MkJoin middle cover) = join th ph in
    MkJoin (Keep Refl middle) (SkipL cover)
  join (Skip th) (Skip ph) =
    let (MkJoin middle cover) = join th ph in
    MkJoin (Skip middle) cover

export
none : {sx : SnocList a} -> Thinning [<] sx
none {sx = [<]} = Empty
none {sx = sx :< x} = Skip none

export
ones : {sx : SnocList a} -> Thinning sx sx
ones {sx = [<]} = Empty
ones {sx = sx :< x} = Keep Refl ones
