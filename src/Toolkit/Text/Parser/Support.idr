|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Toolkit.Text.Parser.Support

import Text.Lexer
import Text.Parser

%default total

public export
Rule : Type -> Type -> Type -> Type
Rule state tok ty = Grammar state tok True ty


public export
RuleEmpty : Type -> Type -> Type -> Type
RuleEmpty state tok ty = Grammar state tok False ty

export
eoi : (f : a -> Bool) -> RuleEmpty state a ()
eoi f
  = ignore $ nextIs "Not End of Input" (f)


-- [ EOF ]
