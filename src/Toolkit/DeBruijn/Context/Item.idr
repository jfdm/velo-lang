||| Context items
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Context.Item

import Decidable.Equality

import Toolkit.Decidable.Informative

%default total

||| An item in our context, paramterised by the type collected.
|||
||| @kind the type of the datatype describing types
||| @type the instance of the type being recorded.
public export
data Item : (type : kind)
                 -> Type
  where
    I : (name : String)
     -> (type : kind)
             -> Item type

||| A generic container to capture properties over items in the
||| context.
public export
data Holds : (kind : Type)
          -> (pred : (type : kind) -> Type)
          -> (key  : String)
          -> {type : kind}
          -> (item : Item type)
                  -> Type
  where
    H : {pred : (type : kind) -> Type}
     -> {i    : kind}
     -> (prfK : key = str)
     -> (prf  : pred i)
             -> Holds kind pred key (I str i)

namespace Holds
  public export
  data Error type = NotSatisfied type
                  | WrongName String String
export
holds : {pred : (type : kind) -> Type}
     -> (func : (type : kind) -> DecInfo err (pred type))
     -> (key  : String)
     -> {type : kind}
     -> (item : Item type)
             -> DecInfo (Holds.Error err)
                        (Holds kind pred key item)
holds func key (I name type) with (decEq key name)
  holds func key (I key type) | (Yes Refl) with (func type)
    holds func key (I key type) | (Yes Refl) | (Yes prfWhy)
      = Yes (H Refl prfWhy)

    holds func key (I key type) | (Yes Refl) | (No msg contra)
      = No (NotSatisfied msg)
           (\(H Refl prf) => contra prf)

  holds func key (I name type) | (No contra)
    = No (WrongName key name)
         (\(H Refl prf) => contra Refl)



-- [ EOF ]
