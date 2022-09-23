||| An embedding of `Dec` instances into `Either` to gain access to Do notation.
|||
||| Thanks Matus for figuring it out.
|||
||| So let's have this:
|||
||| ```
||| exampleDo : DecEq a => DecEq b => (ps, rs : Pair a b) -> Dec (ps = rs)
||| exampleDo (x, y) (a,b)
|||   = decDo $ do Refl <- decEq x a `otherwise` (\Refl => Refl)
|||                Refl <- decEq y b `otherwise` (\Refl => Refl)
|||                Right Refl
||| ```
|||
||| Rather than:
|||
||| ```
||| example : DecEq a => DecEq b => (ps, rs : Pair a b) -> Dec (ps = rs)
||| example (x, y) (a, b) with (decEq x a)
|||   example (x, y) (x, b) | (Yes Refl) with (decEq y b)
|||     example (x, y) (x, y) | (Yes Refl) | (Yes Refl) = Yes Refl
|||     example (x, y) (x, b) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)
|||   example (x, y) (a, b) | (No contra) = No (\Refl => contra Refl)
||| ```
|||
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Decidable.Do

import Decidable.Equality

import Toolkit.Decidable.Informative

%default total

export
otherwise : Dec b -> (a -> b) -> Either (Not a) b
otherwise (Yes pfB)  f = Right pfB
otherwise (No notB)  f = Left (notB . f)

export
decDo : Either (Not a) a -> Dec a
decDo (Left notA) = No notA
decDo (Right pfA) = Yes pfA


-- [ EOF ]
