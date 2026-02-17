(set-logic ALL)

(define-sort Rat () Real)
(define-fun iff ((x Bool) (y Bool)) Bool (= x y))
; Helpers to avoid mixed arithmetic
(define-fun mk_rational ((x Int) (y Int)) Real (/ (to_real x) (to_real y)))
(define-fun zeq ((x Int) (y Int)) Bool (= x y))
(define-fun zleq ((x Int) (y Int)) Bool (<= x y))
(define-fun zlt ((x Int) (y Int)) Bool (< x y))
(define-fun zplus ((x Int) (y Int)) Int (+ x y))
(define-fun zmult ((x Int) (y Int)) Int (* x y))
(define-fun zneg ((x Int)) Int (- x))
(define-fun qeq ((x Real) (y Real)) Bool (= x y))
(define-fun qleq ((x Real) (y Real)) Bool (<= x y))
(define-fun qlt ((x Real) (y Real)) Bool (< x y))
(define-fun qplus ((x Real) (y Real)) Real (+ x y))
(define-fun qmult ((x Real) (y Real)) Real (* x y))
(define-fun qneg ((x Real)) Real (- x))

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

(define-fun teq ((x eo.Term) (y eo.Term)) Bool (= x y))
(define-fun veq ((x vsm.Value) (y vsm.Value)) Bool (= x y))

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
