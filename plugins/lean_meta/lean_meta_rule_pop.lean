module

public import $EO_CALC$.Proofs.RuleSupport.Support
import all $EO_CALC$.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

-- $native-sees Eo Smtm

public theorem cmd_step_pop_$EO_RULE$_properties
    (A : Term) (root : CState) (args : CArgList) (premises : CIndexList) :
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof A = Term.Bool ->
  AllHaveSmtTranslation (premiseTermList root premises) ->
  AllTypeofBool (premiseTermList root premises) ->
  __eo_typeof
      (__eo_cmd_step_pop_proven root CRule.$EO_RULE$ args A premises) =
    Term.Bool ->
  StepPopRuleProperties A (premiseTermList root premises)
    (__eo_cmd_step_pop_proven root CRule.$EO_RULE$ args A premises) :=
by
  sorry
