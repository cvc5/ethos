import Cpc.SmtModel
import Cpc.Logos

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


/- Definitions for theorems -/

/- Definition of refutation -/

inductive eo_is_refutation : Term -> CCmdList -> Prop
$LEAN_EO_IS_REFUTATION_DEF$

/-
A definition of terms in the object language.
This is to be defined externally.
-/
abbrev Object_Term := SmtTerm

/-
A predicate defining a relation on terms in the object language and Booleans
such that (s,b) is true if s evaluates to b.
This is to be defined externally.
-/
abbrev obj_interprets := smt_interprets


/-
Definitions for eo_is_obj
-/
mutual

$LEAN_EO_IS_OBJ_DEFS$

end 

/-
An inductive predicate defining the correspondence between Eunoia terms
and terms in the object language.
(t,s) is true if the Eunoia term represents a term s in the object language.
This is to be custom defined in the Eunoia-to-Lean compiler based on the
target definition of Object_Term.
-/
inductive eo_is_obj : Term -> Object_Term -> Prop
$LEAN_EO_IS_OBJ$

/-
A predicate defining when a Eunoia term corresponds to an object term that
evaluates to true or false.
(t,b) is true if t is a Eunoia term corresponding to an object term that
evaluates to b.
-/
def eo_interprets (t : Term) (b : Bool) : Prop :=
  exists (s : Object_Term), (eo_is_obj t s) /\ (obj_interprets s b)

/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  (eo_is_refutation F pf) ->
  (eo_interprets F false) :=
by
  sorry

/- ---------------------------------------------- -/

