|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Options.ArgParse.Model

%default total

public export
data Arg : Type where
  Flag : String -> Arg
  KeyValue : String -> String -> Arg
  File : String -> Arg

export
Show Arg where
  show (Flag f) = "[Flag " ++ show f ++ "]"
  show (KeyValue k v) = "[KeyValue " ++ show k ++ " : " ++ show v ++ "]"
  show (File fs) = "[File " ++ show fs ++ "]"

-- --------------------------------------------------------------------- [ EOF ]
