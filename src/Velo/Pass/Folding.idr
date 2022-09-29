module Velo.Pass.Folding

import Toolkit.DeBruijn.Context

import Velo.Types
import Velo.Terms

%default total

public export
data FoldsTo : (t, u : Term ctxt ty) -> Type where
  ZeroAdd  : (n : _) -> FoldsTo (Call Add [Call Zero [], n]) n
  AddZero  : (n : _) -> FoldsTo (Call Add [n, Call Zero []]) n
  FalseAnd : (b : _) -> FoldsTo (Call And [Call False [], b]) (Call False [])
  AndFalse : (b : _) -> FoldsTo (Call And [b, Call False []]) (Call False [])
  TrueAnd  : (b : _) -> FoldsTo (Call And [Call True [], b]) b
  AndTrue  : (b : _) -> FoldsTo (Call And [b, Call True []]) b

public export
foldsTo : (t : Term ctx ty) -> Dec (u ** FoldsTo t u)
foldsTo (Call Add [m,n]) with (decEq m (Call Zero []))
  _ | Yes eq = Yes (_ ** rewrite eq in ZeroAdd n)
  _ | No neq1 with (decEq n (Call Zero []))
    _ | Yes eq = Yes (_ ** rewrite eq in AddZero m)
    _ | No neq2 = No $ \ (target ** prf) => case prf of
      ZeroAdd _ => neq1 Refl
      AddZero _ => neq2 Refl
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
foldsTo (Fun body) = No (\case (u ** prf) impossible)
foldsTo (App func arg) = No (\case (u ** prf) impossible) -- TODO: static beta redexes?
foldsTo (Call Zero args) = No (\case (u ** prf) impossible)
foldsTo (Call Plus args) = No (\case (u ** prf) impossible)
foldsTo (Call True args) = No (\case (u ** prf) impossible)
foldsTo (Call False args) = No (\case (u ** prf) impossible)

public export
cfold : Term ctxt ty -> Term ctxt ty

public export
cfolds : All (Term ctxt) tys -> All (Term ctxt) tys
cfolds [] = []
cfolds (arg :: args) = cfold arg :: cfolds args

cfold (Call op args) =
  let args = cfolds args in
  let t = Call op args in
  case foldsTo t of
    Yes (t ** _) => t
    No _ => t
cfold (Fun t) = Fun (cfold t)
cfold (App f t) = App (cfold f) (cfold t)
cfold t = t

-- \f.\b. f (True && (b && False)) (b && True)
-- simplifies to
-- \f.\b. f False b
test : cfold (Fun (Fun (App (App (Var (V 1 (There Here)))
                       (Call And [Call True [], Call And [Var (V 0 Here), Call False []]]))
                       (Call And [Var (V 0 Here), Call True []]))))
     = Fun (Fun (App (App (Var (V 1 (There Here))) (Call False [])) (Var (V 0 Here))))
test = Refl
