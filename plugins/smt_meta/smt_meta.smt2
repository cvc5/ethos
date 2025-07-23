(set-logic UFDTSNIRA)

; tsm.Type:
;   The final embedding of atomic SMT-LIB types that are relevant to the VC.
; sm.Term:
;   The final embedding of atomic SMT-LIB terms that are relevant to the VC.
; eo.Term:
;   The final embedding of Eunoia terms that are relevant to the VC.
;   SMT-LIB terms, types and values are embedded in this datatype. This
;   datatype contains a superset of the Herbrand universe of all types being
;   considered.
;   We require a mutually recursive datatype, since these are
;   inter-dependent.
(declare-datatypes ((tsm.Type 0) (sm.Term 0) (eo.Term 0) (vsm.Value 0) (msm.Map 0))
  (
  (
$SM_TYPE_DECL$
  )
  (
$SM_TERM_DECL$
  )
  (
$SM_EO_TERM_DECL$
  )
  (
$SM_VALUE_DECL$
  )
  (
  ; (msm.Map.cons i e M) maps i -> e, as well as mappings in M
  (msm.Map.cons (msm.Map.cons.arg1 vsm.Value) (msm.Map.cons.arg2 vsm.Value) (msm.Map.cons.arg3 msm.Map))
  ; (msm.Map.default e) maps all remaining elements in the sort to e
  (msm.Map.default (msm.Map.default.arg1 vsm.Value))
  ))
)

;;; Relevant definitions

$SM_DEFS$

;;; Meta-level properties of models

; axiom: $eo_hash
; note: This is defined axiomatically.
(assert (! (forall ((x eo.Term))
  (=> (not (= x eo.Stuck))
    (and
      ((_ is eo.SmtTerm) ($eo_hash x))
      ((_ is sm.Numeral) (eo.SmtTerm.arg1 ($eo_hash x)))))) :named sm.hash_numeral))
(assert (! (forall ((x eo.Term))
    (= ($eo_reverse_hash ($eo_hash x)) x)) :named sm.hash_injective))

; This axiom gives semantics to model lookups for partial functions
(assert (! (forall ((t sm.Term))
  ($smtx_model_lookup_predicate t))
  :named sm.model_lookup_predicate))

;;; The verification condition

$SMT_VC$
