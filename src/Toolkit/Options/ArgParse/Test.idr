|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Options.ArgParse.Test

import Data.String

import Data.Either
import Data.Maybe
import Toolkit.Options.ArgParse
import Toolkit.Options.ArgParse.Error


||| Program Options
record Opts where
  constructor MkOpts
  from    : Maybe String
  verbose : Bool
  help    : Bool
  version : Bool
  args    : List String

Show Opts where
  show (MkOpts f v h ve as) = unwords ["MkOpts", show f, show v, show h, show ve, show as]

Eq Opts where
  (==) (MkOpts a b c d e) (MkOpts a' b' c' d' e') = a == a' && b == b' && c == c' && d' == d' && e == e'

||| Convert Arguments into Options
convOpts : Arg -> Opts -> Maybe Opts
convOpts (File x)     o = Just $ record {args = x :: args o} o
convOpts (KeyValue k v) o =
  case k of
    "from"    => Just $ record {from = Just v} o
    otherwise => Nothing
convOpts (Flag x) o =
  case x of
    "help"    => Just $ record {help = True} o
    "verbose" => Just $ record {verbose = True} o
    "version" => Just $ record {version = True} o
    otherwise => Nothing

defOpts : Opts
defOpts = MkOpts Nothing False False False Nil

test1 : IO ()
test1 =
    case parseArgs defOpts convOpts ["--help", "--verbose"] of
      Left _  => do
        putStrLn "Err"
        pure ()
      Right o => do
        printLn $ (True == verbose o)
        printLn $ (False == help o)
        printLn $ (isNothing $ from o)

export
runTests : IO ()
runTests = do
    putStrLn "Testing ArgParse"
    test1
    printLn (isRight $ parseArgs defOpts convOpts Nil)

    let res' = parseArgs defOpts convOpts ["exe", "--help", "--verbose", "--from=conv"]
    case res' of
      Left _    => putStrLn "Err"
      Right res => do
        printLn (from res == Just "conv")

-- --------------------------------------------------------------------- [ EOF ]
