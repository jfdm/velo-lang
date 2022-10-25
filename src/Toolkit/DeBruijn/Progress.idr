||| How to replace things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.DeBruijn.Progress

import public Toolkit.Data.Relation

%default total

public export
data Progress : (0 value : Pred a)
             -> (0 redux : Rel a)
             -> (tm : a)
                   -> Type
  where
    Done : {0 tm : a}
        -> (val : value tm)
               -> Progress value redux tm

    Step : {this, that : a}
        -> (step       : redux this that)
                      -> Progress value redux this


public export
interface Progressable (0 a : Type)
                       (0 value : Pred a)
                       (0 redux : Rel a)
                               | a
  where
      progress : (tm : a)
                    -> Progress value redux tm

-- [ EOF ]
