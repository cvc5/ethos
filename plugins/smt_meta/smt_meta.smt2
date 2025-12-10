(set-logic UFDTSNIRA)

; eo.Term:
;   The final embedding of Eunoia terms that are relevant to the VC.
;   SMT-LIB terms and types are embedded in this datatype. This
;   datatype contains a superset of the Herbrand universe of all types being
;   considered.
; vsm.Value:
;   A datatype corresponding to SMT-LIB values.
; msm.Map:
;   A datatype corresponding to SMT-LIB map values, for functions and arrays.
; ssm.Seq:
;   A datatype corresponding to SMT-LIB sequence values.
;   We require a mutually recursive datatype, since these are
;   inter-dependent.
(declare-datatypes ((eo.Term 0) (vsm.Value 0) (msm.Map 0) (ssm.Seq 0))
  (
  (
$SM_EO_TERM_DECL$
  )
  (
$SM_VALUE_DECL$
  )
  (
  ; (msm.cons i e M) maps i -> e, as well as mappings in M
  (msm.cons (msm.cons.arg1 vsm.Value) (msm.cons.arg2 vsm.Value) (msm.cons.arg3 msm.Map))
  ; (msm.default e) maps all remaining elements in the sort to e
  (msm.default (msm.default.arg1 vsm.Value))
  )
  (
  ; (ssm.cons i s) is a sequence
  (ssm.cons (ssm.cons.arg1 vsm.Value) (ssm.cons.arg2 ssm.Seq))
  ; the empty sequence
  (ssm.empty)
  )
  )
)

;;; Relevant definitions

$SM_DEFS$

;;; Meta-level properties of models

; axiom for hash
; note: this implies that $smtx_hash is injective, which implies $eo_hash is injective.
(assert (! (forall ((x eo.Term))
    (! (= ($eo_reverse_hash ($smtx_hash x)) x) :pattern (($smtx_hash x)))) :named eo.hash_injective))
(assert (! (forall ((x vsm.Value))
    (! (= ($smtx_reverse_value_hash ($smtx_value_hash x)) x) :pattern (($smtx_value_hash x)))) :named smtx.hash_injective))


;;; The verification condition

$SMT_VC$
