import $EO_CALC$.SmtModel
import $EO_CALC$.LogosTerm

open SmtEval
open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
Definitions for eo_to_smt_type, eo_to_smt
-/
noncomputable section

def native_reserved_datatype_name (s : native_String) : native_Bool :=
  native_string_prefix_eq (native_string_lit "@") s

$LEAN_EO_IS_OBJ_SIMPLE_DEFS$

mutual

$LEAN_EO_IS_OBJ_DEFS$

end

end

/-
Eunoia satisfiability depends on SMT satisfiability.
-/
def eo_satisfiability (t : Term) (b : Bool) : Prop :=
  (smt_satisfiability (__eo_to_smt t) b)


/- ---------------------------------------------- -/
