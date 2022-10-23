||| Borrowed from Frex until Frex and Toolkit's Data are merged into
||| contrib or elsewhere in Idris2's libs/ dir.
module Toolkit.Data.Relation

%default total

public export
0
Pred : Type -> Type
Pred a = a -> Type

public export
0
Rel : Type -> Type
Rel a = a -> a -> Type

infix 5 ~>
public export
0
(~>) : Rel a -> Rel a -> Type
p ~> q = {x, y : a} -> p x y -> q x y

-- [ EOF ]
