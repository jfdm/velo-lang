module Velo.IR.AST

import Data.String
import public Data.Singleton
import Data.List1

import public Toolkit.Data.Location
import public Toolkit.AST

import Velo.Types

%default total


namespace Velo
  public export
  data Kind = EXP

  public export
  data Shape : Kind -> (n : Nat) -> (ss : Vect n Kind)-> Type where
    Ref, Hole  : String -> Shape EXP 0 Nil

    Zero,T,F : Shape EXP 0 Nil

    Plus : Shape EXP 1 [EXP]
    Fun : String -> Ty -> Shape EXP 1 [EXP]
    The : Ty -> Shape EXP 1 [EXP]

    Add,And,App : Shape EXP 2 [EXP, EXP]
    Let : String -> Shape EXP 2 [EXP, EXP]

  public export
  RawUnAnn : Type -> Type
  RawUnAnn = AST Shape EXP

  public export
  Raw : Type
  Raw = AST Shape EXP FileContext

  public export
  RawEmpty : Type
  RawEmpty = AST Shape EXP ()


export
getFC : Raw -> FileContext
getFC = getAnnotation

namespace View
  public export
  data View : Raw -> Type where
    Ref : (fc : FileContext)
       -> (s  : String)
             -> View (Branch (Ref s) fc Nil)

    Hole : (fc : FileContext)
        -> (s  : String)
              -> View (Branch (Hole s) fc Nil)

    Zero : (fc : FileContext)
              -> View (Branch Zero fc Nil)

    Plus : (fc   : FileContext)
        -> (this : View n)
              -> View (Branch Plus fc [n])

    Add : (fc : FileContext)
       -> (left  : View l)
       -> (right : View r)
                -> View (Branch Add fc [l,r])

    True : (fc : FileContext)
              -> View (Branch T fc Nil)

    False : (fc : FileContext)
               -> View (Branch F fc Nil)

    And : (fc : FileContext)
       -> (left  : View l)
       -> (right : View r)
                -> View (Branch And fc [l,r])

    Fun : (fc    : FileContext)
       -> (n     : String)
       -> (ty    : Ty)
       -> (scope : View s)
                -> View (Branch (Fun n ty) fc [s])

    App : (fc  : FileContext)
       -> (fun : View f)
       -> (arg : View a)
              -> View (Branch App fc [f, a])

    Let : (fc    : FileContext)
       -> (n     : String)
       -> (tm    : View expr)
       -> (scope : View body)
                -> View (Branch (Let n) fc [expr, body])

    The : (fc : FileContext)
       -> (ty : Ty)
       -> (tm : View expr)
             -> View (Branch (The ty) fc [expr])

  export
  view : (r : Raw) -> View r
  view (Branch (Ref str) fc Nil)
    = Ref fc str
  view (Branch (Hole str) fc Nil)
    = Hole fc str
  view (Branch Zero fc Nil)
    = Zero fc
  view (Branch T fc Nil)
    = True fc
  view (Branch F fc Nil)
    = False fc
  view (Branch Plus fc [n])
    = Plus fc (view n)
  view (Branch (Fun str ty) fc [scope])
    = Fun fc str ty (view scope)
  view (Branch (The ty) fc [tm])
    = The fc ty (view tm)
  view (Branch Add fc [l,r])
    = Add fc (view l) (view r)
  view (Branch And fc [l,r])
    = And fc (view l) (view r)
  view (Branch App fc [f,a])
    = App fc (view f) (view a)
  view (Branch (Let str) fc [expr,scope])
    = Let fc str (view expr) (view scope)

  export
  getFC : {r : Raw} -> AST.View.View r -> Singleton (getFC r)
  getFC {r} x = Val (getAnnotation r)


-- [ EOF ]
