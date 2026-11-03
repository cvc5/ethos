module

public import $EO_CALC$.SmtEval
import all $EO_CALC$.SmtEval

@[expose] public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

-- $ The syntax of SMT-LIB: what a term and a type are, and the datatypes they
-- $ are built over. What a value is stands in SmtModelDefs, below the static
-- $ interface (SmtTyping, SmtTranslate) that the checker is built on, so that
-- $ the checker never reaches the model semantics.

mutual

/-
SMT-LIB types.
-/
inductive SmtType : Type where
$LEAN_SMT_TYPE_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB terms.
-/
inductive SmtTerm : Type where
$LEAN_SMT_TERM_DEF$
deriving Repr, DecidableEq, Inhabited

-- $ The datatypes of the embedding a type or a term is built over, see
-- $ LeanMetaReduce::printEmbedDatatypes.
$LEAN_SMT_EMBED_DEFS$

end

/- Type equality -/
def native_Teq : SmtType -> SmtType -> native_Bool
  | x, y => decide (x = y)

end Smtm
