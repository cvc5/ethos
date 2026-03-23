import Cpc.SmtModel
import Cpc.Logos
import Cpc.Spec

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


/- The theorem statements -/

/- correctness theorem for __eo_prog_contra -/
theorem correct___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_symm -/
theorem correct___eo_prog_symm (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_symm (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_symm (Proof.pf x1)) true) :=
by
  sorry




/- Helper definitions -/



