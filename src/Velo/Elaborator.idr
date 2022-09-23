module Velo.Elaborator

import Data.Singleton
import Decidable.Equality

import Toolkit.Decidable.Informative

import Velo.Types
import Velo.Terms

import Velo.Core
import Velo.AST

%default total

throwAt : FileContext -> Elaborating.Error -> Velo a
throwAt l e = throw $ Elab (Err l e)

dec : FileContext
   -> Elaborating.Error
   -> Dec     a
   -> Velo a
dec _ _ (Yes prf)
  = pure prf
dec fc err (No _)
  = throwAt fc err

decInfo : FileContext
       -> Elaborating.Error
       -> DecInfo e a
       -> Velo   a
decInfo _ _ (Yes prf)
  = pure prf
decInfo fc e (No msg prf)
  = throwAt fc e

compare : (fc  : FileContext)
       -> (a,b : Ty)
              -> Velo (a = b)
compare fc a b
  = dec fc (Mismatch a b)
           (decEq    a b)

Context : List Ty -> Type
Context = Context Ty

elab : {types : List Ty}
    -> (ctxt  : Context types)
    -> (expr  : (AST FileContext))
             -> Velo (DPair Ty (Term types))
elab ctxt (Ref fc str)
  = do prf <- decInfo
                fc
                (NotBound str)
                (lookup str ctxt)
       let (ty ** loc ** prfN) = deBruijn prf
       pure (ty ** Var (V loc prfN))

elab ctxt (Zero _)
  = pure (TyNat ** Zero)

elab ctxt (Plus fc e)
  = do (ty ** tm) <- elab ctxt e
       Refl <- compare fc TyNat ty
       pure (TyNat ** Plus tm)

elab ctxt (Add fc x y)
  = do (tyX ** x) <- elab ctxt x
       Refl <- compare fc TyNat tyX

       (tyY ** y) <- elab ctxt y
       Refl <- compare fc TyNat tyY

       pure (TyNat ** (Add x y))

elab ctxt (T _)
  = pure (TyBool ** True)
elab ctxt (F _)
  = pure (TyBool ** False)

elab ctxt (And fc x y)
  = do (tyX ** x) <- elab ctxt x
       Refl <- compare fc TyBool tyX

       (tyY ** y) <- elab ctxt y
       Refl <- compare fc TyBool tyY

       pure (TyBool ** (And x y))

elab ctxt (Let fc str v scope)
  = do (ty ** v) <- elab ctxt v
       (tyS ** scope) <- elab (extend ctxt str ty) scope

       pure (tyS ** App (Fun scope) v)

elab ctxt (Fun fc str ty scope)
  = do (tyS ** scope) <- elab (extend ctxt str ty) scope

       pure (TyFunc ty tyS ** Fun scope)

elab ctxt (App fc f a)
  = do (TyFunc tyAE tyB ** f) <- elab ctxt f
         | (ty ** tm) => throwAt fc (FuncExpected ty)

       (tyAG ** a) <- elab ctxt a

       Refl <- compare fc tyAE tyAG

       pure (_ ** App f a)

elab ctxt (The fc tyE tm)
  = do (tyG ** tm) <- elab ctxt tm
       Refl <- compare fc tyE tyG
       pure (_ ** tm)

namespace Closed
  export
  elab : (e : AST FileContext)
           -> Velo (DPair Ty (Term Nil))
  elab e = elab Nil e

-- [ EOF ]
