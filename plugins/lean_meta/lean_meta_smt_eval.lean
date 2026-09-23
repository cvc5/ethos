module

public import Init

public section

set_option linter.unusedVariables false

namespace SmtEval

-- $ Not a block of the native layer: SmtValue carries a Rational constructor
-- $ whatever the input signature is, and derives Ord, so this instance is
-- $ needed whatever an input reaches and is written here rather than in
-- $ lean.eos.
instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

-- The primitive operations every other module is written over.
-- $ The part of the native layer the compilation reached that is Lean and
-- $ nothing else, see LeanMetaReduce::nativeDefs.
$NATIVE_DEFS$

end SmtEval
