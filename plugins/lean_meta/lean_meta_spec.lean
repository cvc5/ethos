module

public import $EO_CALC$.SmtTranslate
import all $EO_CALC$.SmtTranslate
public import $EO_CALC$.SmtModel
import all $EO_CALC$.SmtModel

@[expose] public section

open SmtEval
open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
Eunoia satisfiability depends on SMT satisfiability.
-/
def eo_satisfiability (t : Term) (b : Bool) : Prop :=
  (smt_satisfiability (__eo_to_smt t) b)

/- ---------------------------------------------- -/
