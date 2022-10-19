module Velo.Pass.Folding

import Decidable.Equality
import Toolkit.DeBruijn.Variable

import Velo.Types
import Velo.IR.Common
import Velo.IR.Term

%default total

public export
data FoldsTo : (t, u : Term metas ctxt ty) -> Type where
  ZeroAdd  : (n : _) -> FoldsTo (Call Add [Call Zero [], n]) n
  AddZero  : (n : _) -> FoldsTo (Call Add [n, Call Zero []]) n
  FalseAnd : (b : _) -> FoldsTo (Call And [Call False [], b]) (Call False [])
  AndFalse : (b : _) -> FoldsTo (Call And [b, Call False []]) (Call False [])
  TrueAnd  : (b : _) -> FoldsTo (Call And [Call True [], b]) b
  AndTrue  : (b : _) -> FoldsTo (Call And [b, Call True []]) b

public export
foldsTo : (t : Term metas ctx ty) -> Dec (u ** FoldsTo t u)
foldsTo (Call Add [m,n]) with (decEq m (Call Zero []))
  _ | Yes eq = Yes (_ ** rewrite eq in ZeroAdd n)
  _ | No neq1 with (decEq n (Call Zero []))
    _ | Yes eq = Yes (_ ** rewrite eq in AddZero m)
    _ | No neq2 = No $ \ (target ** prf) => case prf of
      ZeroAdd _ => neq1 Refl
      AddZero _ => neq2 Refl
      FalseAnd impossible
      AndFalse impossible
      TrueAnd impossible
      AndTrue impossible
foldsTo (Call And [b,c]) with (decEq b (Call False []))
  _ | Yes eq = Yes (_ ** rewrite eq in FalseAnd c)
  _ | No neq1 with (decEq c (Call False []))
    _ | Yes eq = Yes (_ ** rewrite eq in AndFalse b)
    _ | No neq2 with (decEq b (Call True []))
      _ | Yes eq = Yes (_ ** rewrite eq in TrueAnd c)
      _ | No neq3 with (decEq c (Call True []))
        _ | Yes eq = Yes (_ ** rewrite eq in AndTrue b)
        _ | No neq4 = No $ \ (target ** prf) => case prf of
          FalseAnd _ => neq1 Refl
          AndFalse _ => neq2 Refl
          TrueAnd _ => neq3 Refl
          AndTrue _ => neq4 Refl
          ZeroAdd _ impossible
          AddZero _ impossible

foldsTo (Var prf) = No (\case (u ** prf) impossible)
foldsTo (Met prf sg) = No (\case (u ** prf) impossible)
foldsTo (Fun body) = No (\case (u ** prf) impossible)
foldsTo (Call App args) = No (\case (u ** prf) impossible)
foldsTo (Call Zero args) = No (\case (u ** prf) impossible)
foldsTo (Call Plus args) = No (\case (u ** prf) impossible)
foldsTo (Call True args) = No (\case (u ** prf) impossible)
foldsTo (Call False args) = No (\case (u ** prf) impossible)

public export
cfold : Term metas ctxt ty -> Term metas ctxt ty

public export
cfolds : {0 tys : List Ty} -> All (Term metas ctxt) tys -> All (Term metas ctxt) tys
cfolds [] = []
cfolds (arg :: args) = cfold arg :: cfolds args

cfold (Call op args) =
  let args = cfolds args in
  let t = Call op args in
  case foldsTo t of
    Yes (t ** _) => t
    No _ => t
cfold (Fun t) = Fun (cfold t)
cfold t = t

-- \f.\b. f (True && (b && False)) (b && True)
-- simplifies to
-- \f.\b. f False b
test : cfold (Fun (Fun $
         Call App [ Call App [ Var (shift Variable.here)
                             , Call And [ Call True []
                                        , Call And [Var Variable.here
                                                  , Call False []]]]
                  , Call And [Var Variable.here, Call True []]]))
     = Fun (Fun (Call App [Call App [ Var (shift Variable.here)
                                    , Call False []]
                          , Var Variable.here]))
test = Refl
