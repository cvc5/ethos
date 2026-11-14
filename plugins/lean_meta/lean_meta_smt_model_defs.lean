module

public import $EO_CALC$.SmtReal
import all $EO_CALC$.SmtReal
public import $EO_CALC$.SmtSyntax
import all $EO_CALC$.SmtSyntax

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

-- $ Equality of the reals is classical, so what is derived from it is
-- $ noncomputable and there is neither a Repr nor an Ord to derive.
noncomputable section

mutual

/-
SMT-LIB values.
-/
inductive SmtValue : Type where
$LEAN_SMT_VALUE_DEF$
deriving DecidableEq, Inhabited

-- $ The datatypes a value is built over -- the map, the sequence and the
-- $ regular language. Which of them there are and what builds one is the
-- $ target's to declare, see declare-embed-datatype in
-- $ plugins/model_smt/model_smt.eos; which of them stand here rather than in
-- $ SmtSyntax is read off their constructors, see
-- $ LeanMetaReduce::isSyntaxDatatype.
$LEAN_SMT_EMBED_DEFS$

end

-- Equality of a value, decided by the inductive above. It stands after the
-- mutual block rather than beside the inductive whose `deriving` makes it
-- possible: a mutual block holds inductives or definitions, never both.

/- Value equality -/
def native_veq : SmtValue -> SmtValue -> native_Bool
  | x, y => decide (x = y)

end

end Smtm
