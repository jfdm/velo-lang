|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Data.Fin

import public Decidable.Equality
import public Data.Fin


%default total

namespace Safe

  ||| Safe nat to fin conversion
  public export
  data NatToFin : (n,m : Nat) -> Fin m -> Type where
    Here : NatToFin Z (S _) FZ
    There : NatToFin k j f
         -> NatToFin (S k) (S j) (FS f)

  bothZero : (f : Fin 0 ** NatToFin 0 0 f) -> Void
  bothZero (FZ ** _) impossible

  upZero :  (f : Fin 0 ** NatToFin (S k) 0 f) -> Void
  upZero (FZ ** _) impossible

  export
  natToFin : (n,m : Nat) -> Dec (f : Fin m ** NatToFin n m f)
  natToFin 0 0
    = No bothZero
  natToFin 0 (S k)
    = Yes (FZ ** Here)

  natToFin (S k) 0
    = No upZero
  natToFin (S k) (S j) with (Safe.natToFin k j)
    natToFin (S k) (S j) | (Yes ((fst ** snd)))
      = Yes (FS fst ** There snd)
    natToFin (S k) (S j) | (No contra)
      = No (\(FS f ** There rest) => contra (f ** rest))

-- [ EOF ]
