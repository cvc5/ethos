module

public import Init

public section

set_option linter.unusedVariables false

namespace SmtEval

-- The primitive operations every other module is written over.
-- $ The part of the native layer the compilation reached that is Lean and
-- $ nothing else, see LeanMetaReduce::nativeDefs.
$NATIVE_DEFS$

end SmtEval
