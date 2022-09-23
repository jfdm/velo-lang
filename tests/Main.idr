module Main

import Data.List

import Test.Golden

%default total

working : IO TestPool
working
  = testsInDir "working"
               (const True)
               "Passing Tests"
               []
               Nothing

covering
main : IO ()
main
  = runner [ !working
           ]

-- [ EOF ]
