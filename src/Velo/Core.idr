module Velo.Core

import        System

import        Data.String

import public Toolkit.TheRug
import        Toolkit.System

import public Velo.Error
import        Velo.Error.Pretty

%default total

public export
%inline
Velo : Type -> Type
Velo = TheRug Velo.Error



namespace Velo

  %inline
  whenErr : (msg : Velo.Error)
                -> IO ()
  whenErr err
    = do putStrLn (show err)
         exitWith (ExitFailure 1)

  %inline
  whenOK : a -> IO ()
  whenOK _ = pure ()

  export
  run : (prog : Velo a)
             -> IO ()
  run = run whenErr whenOK

-- [ EOF ]
