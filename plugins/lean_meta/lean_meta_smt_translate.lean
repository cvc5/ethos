module

public import $EO_CALC$.SmtTyping
import all $EO_CALC$.SmtTyping
public import $EO_CALC$.LogosTerm
import all $EO_CALC$.LogosTerm

@[expose] public section

open SmtEval
open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


/-
Definitions for eo_to_smt_type, eo_to_smt
-/
noncomputable section

$LEAN_EO_IS_OBJ_SIMPLE_DEFS$

mutual

$LEAN_EO_IS_OBJ_DEFS$

end

end
