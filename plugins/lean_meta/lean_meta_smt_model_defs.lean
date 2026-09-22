module

public import $EO_CALC$.SmtEval
import all $EO_CALC$.SmtEval

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

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

/-
SMT-LIB values.
-/
inductive SmtValue : Type where
$LEAN_SMT_VALUE_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

-- $ The datatypes a value is built over -- the map, the sequence, the regular
-- $ language and the three a datatype declaration is made of. Which of them
-- $ there are and what builds one is the target's to declare, see
-- $ declare-embed-datatype in plugins/model_smt/model_smt.eos, so the
-- $ inductives are generated with the three above rather than written here.
$LEAN_SMT_EMBED_DEFS$

end

-- Equality of a type and of a value, decided by the two inductives above.
-- They stand after the mutual block rather than beside the inductive whose
-- `deriving` makes them possible: a mutual block holds inductives or
-- definitions, never both.

/- Type equality -/
def native_Teq : SmtType -> SmtType -> native_Bool
  | x, y => decide (x = y)

/- Value equality -/
def native_veq : SmtValue -> SmtValue -> native_Bool
  | x, y => decide (x = y)

end Smtm
