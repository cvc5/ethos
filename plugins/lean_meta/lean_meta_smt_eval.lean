module

public import Init

public section

set_option linter.unusedVariables false

namespace SmtEval

-- Not a block: SmtValue carries a Rational constructor whatever the input
-- signature is, and derives Ord, so this instance is always needed.
instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

-- The part of the native layer that is Lean and nothing else, which every
-- generated module has in scope.
$NATIVE_DEFS$

end SmtEval
