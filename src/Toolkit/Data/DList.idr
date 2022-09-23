||| A `list` construct to create lists of dependent types.
|||
||| One of the problems with using dependent types is that types
||| depend on values. This affects the ability to construct lists of
||| values that have a dependent type. The existing `List` type cannot
||| be used as it requires all elements to have the same type.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.DList

import        Data.String
import public Data.List
import public Data.List.Elem

||| A list construct for dependent types.
|||
||| @aTy    The type of the value contained within the list element type.
||| @elemTy The type of the elements within the list
||| @as     The List used to contain the different values within the type.
public export
data DList : (aTy : Type)
          -> (elemTy : aTy -> Type)
          -> (as : List aTy)
          -> Type where
  ||| Create an empty List
  Nil  : DList aTy elemTy Nil
  ||| Cons
  |||
  ||| @elem The element to add
  ||| @rest The list for `elem` to be added to.
  (::) : {x : aTy}
      -> (elem : elemTy x)
      -> (rest : DList aTy elemTy xs)
      -> DList aTy elemTy (x::xs)


public export
mapToList : (forall x . e x -> b)
         -> DList a e xs
         -> List b
mapToList _ Nil = Nil
mapToList f (x::xs) = f x :: mapToList f xs

public export
lookup : (idx : Elem x xs)
      -> (ps  : DList type pred xs)
             -> pred x
lookup Here (elem :: rest) = elem
lookup (There y) (elem :: rest) = lookup y rest

public export
replace : (idx : Elem x xs)
       -> (new : pred x)
       -> (ps  : DList type pred xs)
              -> DList type pred xs
replace Here new (elem :: rest) = new :: rest
replace (There y) new (elem :: rest) = elem :: replace y new rest

||| Function to show a `DList`.
|||
||| Due to limitations in idris wrt to class instances on dependent
||| types a generic show instance cannot be defined for
||| sigmalist. This will cause minor annoyances in its use.
|||
||| @showFunc A function to show the elements
||| @l       The list to be Shown.
public export
showDList : (showFunc : forall a . elemTy a -> String)
         -> (l : DList aTy elemTy as)
         -> String
showDList f xs = "[" ++ unwords (intersperse "," (mapToList f xs)) ++ "]"


namespace Alt
  public export
  index : (xs  : DList iTy eTy is)
       -> (idx : Elem i is)
       -> eTy i
  index (ex :: rest) Here = ex
  index (ex :: rest) (There later) = index rest later

  public export
  update : (vs  : DList iTy eTy is)
        -> (idx : Elem i is)
        -> (new : eTy i)
        -> DList iTy eTy is
  update (ex :: rest) Here new = new :: rest
  update (ex :: rest) (There later) new = ex :: update rest later new


  public export
  updateWith : DList iTy eTy is
            -> Elem i is
            -> (eTy i -> eTy i)
            -> DList iTy eTy is
  updateWith (ex :: rest) Here f = f ex :: rest
  updateWith (ex :: rest) (There later) f = ex :: updateWith rest later f

-- --------------------------------------------------------------------- [ EOF ]
