module

public import $EO_CALC$.SmtSyntax
import all $EO_CALC$.SmtSyntax

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

mutual

/-
SMT-LIB values.
-/
inductive SmtValue : Type where
$LEAN_SMT_VALUE_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

-- $ The datatypes a value is built over -- the map, the sequence and the
-- $ regular language. Which of them there are and what builds one is the
-- $ target's to declare, see declare-embed-datatype in
-- $ plugins/model_smt/model_smt.eos; which of them stand here rather than in
-- $ SmtSyntax is read off their constructors, see
-- $ LeanMetaReduce::printEmbedDatatypes.
$LEAN_SMT_EMBED_DEFS$

end

-- Equality of a value, decided by the inductive above. It stands after the
-- mutual block rather than beside the inductive whose `deriving` makes it
-- possible: a mutual block holds inductives or definitions, never both.

/- Value equality -/
def native_veq : SmtValue -> SmtValue -> native_Bool
  | x, y => decide (x = y)

end Smtm
