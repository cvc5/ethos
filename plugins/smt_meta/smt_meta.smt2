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
(declare-datatypes ((tsm.Type 0) (sm.Term 0) (eo.Term 0) (vsm.Value 0) (msm.Map 0) (seq.Seq 0))
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
  ; (msm.cons i e M) maps i -> e, as well as mappings in M
  (msm.cons (msm.cons.arg1 vsm.Value) (msm.cons.arg2 vsm.Value) (msm.cons.arg3 msm.Map))
  ; (msm.default e) maps all remaining elements in the sort to e
  (msm.default (msm.default.arg1 vsm.Value))
  )
  (
  ; (seq.cons i s) is a sequence
  (seq.cons (seq.cons.arg1 vsm.Value) (seq.cons.arg2 seq.Seq))
  ; the empty sequence
  (seq.empty)
  )
  )
)

;;; Relevant definitions

$SM_DEFS$

;;; Meta-level properties of models

; axiom for hash
; note: this implies that $smtx_hash is injective, which implies $eo_hash is injective.
(assert (! (forall ((x eo.Term))
    (= ($eo_reverse_hash ($smtx_hash x)) x)) :named eo.hash_injective))

;;; The verification condition

$SMT_VC$
