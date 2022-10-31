module Velo.Core

import        System

import        Data.String

import public Toolkit.TheRug
import public Toolkit.TheRug.Logging.Simple
import        Toolkit.System

import public Velo.Error
import        Velo.Error.Pretty

import public Toolkit.Data.Location

%default total

public export
%inline
Velo : Type -> Type
Velo = TheRug Velo.Error

export
throwAt : FileContext -> Elaborating.Error -> Velo a
throwAt l e = throw $ Elab (Err l e)

export
dec : FileContext
   -> Elaborating.Error
   -> Dec     a
   -> Velo a
dec _ _ (Yes prf)
  = pure prf
dec fc err (No _)
  = throwAt fc err

namespace Velo

  %inline
  whenErr : (msg : Velo.Error)
                -> IO ()
  whenErr err
    = do printLn err
         exitFailure

  %inline
  whenOK : a -> IO ()
  whenOK _ = pure ()

  export
  run : (prog : Velo a)
             -> IO ()
  run = run whenErr whenOK

-- [ EOF ]
