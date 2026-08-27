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

-- A proof written against the published tree names its strings with this, so
-- it is kept for a signature that has no string of its own to build.
-- $native-root native_string_lit

-- The part of the native layer that every generated file can see. What comes
-- out here is what more than one of them reaches, since a definition only one
-- reaches is emitted into that file instead. See
-- LeanMetaReduce::placeNativeDefs and plugins/lean_meta/lean_meta_native.lean.
-- $native-place SmtEval

end SmtEval
