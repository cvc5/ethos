module

public import $EO_CALC$.SmtSyntax
import all $EO_CALC$.SmtSyntax

@[expose] public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

-- The static interface of SMT-LIB: typing and well-formedness. Nothing here
-- names a value or a model, so the checker, which computes these, is built
-- without the model semantics.
-- $ What of the semantics comes out here rather than in SmtModel is read off
-- $ what each program names, see LeanMetaReduce::finalizeSmtPrograms.

-- The primitive operations the static interface uses and no module above it.
-- $ See LeanMetaReduce::nativeDefs.
$NATIVE_DEFS$

/- Definition of the static interface of SMT-LIB -/

$LEAN_SMT_TYPING_DEFS$

end Smtm
