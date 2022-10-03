module Toolkit.Data.List.Thinning

import public Toolkit.Data.List.Subset

public export
Thinning : (xs, ys : List a) -> Type
Thinning = Subset (===)

export
Identity : {xs : List a} -> Thinning xs xs
Identity {xs = []} = Empty
Identity {xs = x :: xs} = Keep Refl Identity

infixr 8 <.>
export
(<.>) : Thinning xs ys -> Thinning ys zs -> Thinning xs zs
(<.>) = trans (\ eq1, eq2 => trans eq1 eq2)

namespace Cover

  public export
  data Cover : (th : Thinning {a} xs1 ys) -> (ph : Thinning xs2 ys) -> Type where
    Empty : Cover Empty Empty
    Keep  : Cover th ph -> Cover (Keep Refl th) (Keep Refl ph)
    SkipL : Cover th ph -> Cover (Skip th) (Keep Refl ph)
    SkipR : Cover th ph -> Cover (Keep eq th) (Skip ph)

  export
  coverDec : (th : Thinning {a} xs1 ys) -> (ph : Thinning xs2 ys) -> Dec (Cover th ph)
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
    {a : Type} {xs1, xs2, ys : List a}
    (th : Thinning xs1 ys)
    (ph : Thinning xs2 ys) where
    constructor MkJoin
    {union : List a}
    {left   : Thinning xs1 union}
    middle : Thinning union ys
    {right  : Thinning xs2 union}
    cover  : Cover left right

  export
  join : {ys : _} -> (th : Thinning xs1 ys) -> (ph : Thinning xs2 ys) -> Join th ph
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
none : {xs : List a} -> Thinning [] xs
none {xs = []} = Empty
none {xs = x :: xs} = Skip none

export
ones : {xs : List a} -> Thinning xs xs
ones {xs = []} = Empty
ones {xs = x :: xs} = Keep Refl ones
