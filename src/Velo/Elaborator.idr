module Velo.Elaborator

import Data.Singleton
import Decidable.Equality

import Toolkit.Decidable.Informative

import Velo.Types
import Velo.Terms
import Velo.Terms.Holes

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

public export
data Hole : (Ty, List Ty) -> Type where
  H : (fc   : FileContext)
   -> (str  : String)
   -> (type : Ty)
   -> (ctxt : Context Ty types)
           -> Hole (type, types)

public export
Holes : List (Ty, List Ty) -> Type
Holes = DList (Ty, List Ty) Hole

data Result : (holes : List (Ty, List Ty))
           -> (ctxt  : List Ty)
                    -> Ty
                    -> Type
  where
    R : {new   : List (Ty , List Ty)}
     -> (holes : Holes      new)
     -> (tm    : Term   old new ctxt ty)
              -> Result old     ctxt ty

mutual
  synth : {types : List Ty}
       -> {holes : List (Ty, List Ty)}
       -> (eta   : Holes   holes)
       -> (ctxt  : Context types)
       -> (expr  : (AST FileContext))
                -> Velo (DPair Ty (Result holes types))

  synth eta ctxt (Ref fc str)
    = do prf <- decInfo
                  fc
                  (NotBound str)
                  (lookup str ctxt)
         let (ty ** loc ** prfN) = deBruijn prf
         pure (ty ** R eta (Var (V loc prfN)))

  synth eta ctxt (Hole fc str)
    = throwAt fc (Hole "Not supposed to get here.")

  synth eta ctxt (Zero fc)
    = pure (TyNat ** R eta Zero)

  synth eta ctxt (Plus fc nat)
    = do (R eta tm) <- check eta ctxt TyNat nat

         pure (TyNat ** R eta (Plus tm))

  synth eta ctxt (Add fc x y)
    = do R ex x <- check eta ctxt TyNat x
         R ey y <- check ex  ctxt TyNat y

         pure (TyNat ** R ey (Add x y))

  synth eta ctxt (T _)
    = pure (TyBool ** R eta True)

  synth eta ctxt (F _)
    = pure (TyBool ** R eta False)

  synth eta ctxt (And fc x y)
    = do R ex x <- check eta ctxt TyBool x
         R ey y <- check ex  ctxt TyBool y

         pure (TyBool ** R ey (And x y))

  synth eta ctxt (Let fc str v scope)
    = do (ty  ** R ev v) <- synth eta ctxt v

         (tys ** R es scope) <- synth ev (extend ctxt str ty) scope

         pure (tys ** R es (Let v scope))

  synth eta ctxt (Fun fc str ty scope)
    = do (tyS ** R e scope) <- synth eta (extend ctxt str ty) scope

         pure (TyFunc ty tyS ** R e (Fun scope))

  synth eta ctxt (App fc f a)
    = do (TyFunc tyA tyB ** R e f) <- synth eta ctxt f
           | (ty ** tm) => throwAt fc (FuncExpected ty)

         R e a <- check e ctxt tyA a

         pure (_ ** R e (App f a))

  synth eta ctxt (The fc ty tm)
    = do R e tm <- check eta ctxt ty tm
         pure (ty ** R e tm)

  check : {types : List Ty}
       -> {holes : List (Ty, List Ty)}
       -> (eta   : Holes   holes)
       -> (ctxt  : Context types)
       -> (ty    : Ty)
       -> (expr  : (AST FileContext))
                -> Velo (Result holes types ty)
  check eta ctxt ty (Hole fc str)
    = pure (R (H fc str ty ctxt :: eta) Hole)
  check eta ctxt tyE rest
    = do (tyG ** R eta tm) <- synth eta ctxt rest
         Refl <- compare (getFC rest) tyE tyG
         pure (R eta tm)

data Elab : Term i o xs type
           -> Term     xs type
           -> Type
  where
    Var : Elab (Var prf) (Var prf)
    Fun : Elab scope scope'
       -> Elab (Fun scope) (Fun scope')
    Let : Elab val v
       -> Elab scope s
       -> Elab (Let val scope) (App (Fun s) v)
    App : Elab func f
       -> Elab arg  a -> Elab (App func arg) (App f a)

    Zero : Elab Zero (Call Zero [])

    Plus : Elab nat n -> Elab (Plus nat) (Call Plus [n])

    Add : Elab left l
       -> Elab right r
       -> Elab (Add left right) (Call Add [l, r])

    True : Elab True (Call True [])
    False : Elab False (Call False [])

    And : Elab left l
       -> Elab right r
       -> Elab (And left right) (Call And [l, r])

Uninhabited (Elab Hole h) where
  uninhabited (Var) impossible
  uninhabited (Fun x) impossible
  uninhabited (Let x y) impossible
  uninhabited (App x y) impossible
  uninhabited (Zero) impossible
  uninhabited (Plus x) impossible
  uninhabited (Add x y) impossible
  uninhabited (True) impossible
  uninhabited (False) impossible
  uninhabited (And x y) impossible

elab : (term : Term i o xs type)
            -> Dec (DPair (Term xs type) (Elab term))
elab (Var prf)
  = Yes (Var prf ** Var)
elab Hole
  = No (\(tm ** body) => absurd body)

elab (Fun body) with (elab body)
  elab (Fun body) | (Yes ((fst ** snd)))
    = Yes (Fun fst ** Fun snd)
  elab (Fun body) | (No no)
    = No (\(Fun b ** Fun body) => no (b ** body))

elab (Let val scope) with (elab val)
  elab (Let val scope) | (Yes (v ** prfV)) with (elab scope)
    elab (Let val scope) | (Yes (v ** prfV)) | (Yes (s ** prfS))
      = Yes (App (Fun s) v ** Let prfV prfS)

    elab (Let val scope) | (Yes (v ** prfV)) | (No no)
      = No (\(App (Fun s) v ** Let x sc) => no (s ** sc))

  elab (Let val scope) | (No no)
    = No (\(App (Fun s) v ** Let x sc) => no (v ** x))

elab (App func arg) with (elab func)
  elab (App func arg) | (Yes (f ** prfF)) with (elab arg)
    elab (App func arg) | (Yes (f ** prfF)) | (Yes (a ** prfA))
      = Yes (App f a ** App prfF prfA)
    elab (App func arg) | (Yes (f ** prfF)) | (No no)
      = No (\(App f a ** App pF pA) => no (a ** pA))
  elab (App func arg) | (No no)
    = No (\(App f a ** App pF pA) => no (f ** pF))

elab Zero
  = Yes (Call Zero [] ** Zero)

elab (Plus x) with (elab x)
  elab (Plus x) | (Yes ((fst ** snd)))
    = Yes (Call Plus [fst] ** Plus snd)
  elab (Plus x) | (No no)
    = No (\(Call Plus [x] ** Plus s) => no (x ** s))

elab (Add l r) with (elab l)
  elab (Add l r) | (Yes (l' ** pl)) with (elab r)
    elab (Add l r) | (Yes (l' ** pl)) | (Yes (r' ** pr))
      = Yes (Call Add [l', r'] ** Add pl pr)
    elab (Add l r) | (Yes (l' ** pl)) | (No no)
      = No (\(Call Add [l, r] ** Add pl pr) => no (r ** pr))
  elab (Add l r) | (No no)
    = No (\(Call Add [l, r] ** Add pl pr) => no (l ** pl))

elab True
  = Yes (Call True [] ** True)
elab False
  = Yes (Call False [] ** False)

elab (And l r) with (elab l)
  elab (And l r) | (Yes (l' ** pl)) with (elab r)
    elab (And l r) | (Yes (l' ** pl)) | (Yes (r' ** pr))
      = Yes (Call And [l', r'] ** And pl pr)
    elab (And l r) | (Yes (l' ** pl)) | (No no)
      = No (\(Call And [l, r] ** And pl pr) => no (r ** pr))
  elab (And l r) | (No no)
    = No (\(Call And [l, r] ** And pl pr) => no (l ** pl))


namespace Closed
  public export
  data Result : Type where
    Closed : {type : Ty} -> (term  : Term Nil type) -> Result
    Holly  : (holes : Holes hs) -> Result
  export
  elab : (e : AST FileContext)
           -> Velo Result
  elab e
    = do (ty ** R Nil tm) <- synth Nil Nil e
           | (_ ** R holes _)
             => pure (Holly holes)
         (tm ** prf) <- embed (Internal "Holes found, should not happen")
                             (elab tm)
         pure (Closed tm)

-- [ EOF ]
