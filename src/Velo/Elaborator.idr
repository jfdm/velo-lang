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

data UnHoly : Term i o xs type
           -> Term     xs type
           -> Type
  where
    Var : UnHoly (Var prf) (Var prf)
    Fun : UnHoly scope scope'
       -> UnHoly (Fun scope) (Fun scope')
    Let : UnHoly val v
       -> UnHoly scope s
       -> UnHoly (Let val scope) (App (Fun s) v)
    App : UnHoly func f
       -> UnHoly arg  a -> UnHoly (App func arg) (App f a)

    Zero : UnHoly Zero Zero

    Plus : UnHoly nat n -> UnHoly (Plus nat) (Plus n)

    Add : UnHoly left l
       -> UnHoly right r
       -> UnHoly (Add left right) (Add l r)

    True : UnHoly True True
    False : UnHoly False False

    And : UnHoly left l
       -> UnHoly right r
       -> UnHoly (And left right) (And l r)

Uninhabited (UnHoly Hole h) where
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

unHoly : (term : Term i o xs type)
              -> Dec (DPair (Term xs type) (UnHoly term))
unHoly (Var prf)
  = Yes (Var prf ** Var)
unHoly Hole
  = No (\(tm ** body) => absurd body)

unHoly (Fun body) with (unHoly body)
  unHoly (Fun body) | (Yes ((fst ** snd)))
    = Yes (Fun fst ** Fun snd)
  unHoly (Fun body) | (No no)
    = No (\(Fun b ** Fun body) => no (b ** body))

unHoly (Let val scope) with (unHoly val)
  unHoly (Let val scope) | (Yes (v ** prfV)) with (unHoly scope)
    unHoly (Let val scope) | (Yes (v ** prfV)) | (Yes (s ** prfS))
      = Yes (App (Fun s) v ** Let prfV prfS)

    unHoly (Let val scope) | (Yes (v ** prfV)) | (No no)
      = No (\(App (Fun s) v ** Let x sc) => no (s ** sc))

  unHoly (Let val scope) | (No no)
    = No (\(App (Fun s) v ** Let x sc) => no (v ** x))

unHoly (App func arg) with (unHoly func)
  unHoly (App func arg) | (Yes (f ** prfF)) with (unHoly arg)
    unHoly (App func arg) | (Yes (f ** prfF)) | (Yes (a ** prfA))
      = Yes (App f a ** App prfF prfA)
    unHoly (App func arg) | (Yes (f ** prfF)) | (No no)
      = No (\(App f a ** App pF pA) => no (a ** pA))
  unHoly (App func arg) | (No no)
    = No (\(App f a ** App pF pA) => no (f ** pF))

unHoly Zero
  = Yes (Zero ** Zero)

unHoly (Plus x) with (unHoly x)
  unHoly (Plus x) | (Yes ((fst ** snd)))
    = Yes (Plus fst ** Plus snd)
  unHoly (Plus x) | (No no)
    = No (\(Plus x ** Plus s) => no (x ** s))

unHoly (Add l r) with (unHoly l)
  unHoly (Add l r) | (Yes (l' ** pl)) with (unHoly r)
    unHoly (Add l r) | (Yes (l' ** pl)) | (Yes (r' ** pr))
      = Yes (Add l' r' ** Add pl pr)
    unHoly (Add l r) | (Yes (l' ** pl)) | (No no)
      = No (\(Add l r ** Add pl pr) => no (r ** pr))
  unHoly (Add l r) | (No no)
    = No (\(Add l r ** Add pl pr) => no (l ** pl))

unHoly True
  = Yes (True ** True)
unHoly False
  = Yes (False ** False)

unHoly (And l r) with (unHoly l)
  unHoly (And l r) | (Yes (l' ** pl)) with (unHoly r)
    unHoly (And l r) | (Yes (l' ** pl)) | (Yes (r' ** pr))
      = Yes (And l' r' ** And pl pr)
    unHoly (And l r) | (Yes (l' ** pl)) | (No no)
      = No (\(And l r ** And pl pr) => no (r ** pr))
  unHoly (And l r) | (No no)
    = No (\(And l r ** And pl pr) => no (l ** pl))


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
                             (unHoly tm)
         pure (Closed tm)

-- [ EOF ]
