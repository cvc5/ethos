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
(define-fun streq ((x String) (y String)) Bool (= x y))
(define-fun /_by_zero ((x Real)) Real (/ x 0.0))
(define-fun div_by_zero ((x Int)) Int (div x 0))
(define-fun mod_by_zero ((x Int)) Int (mod x 0))

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
(declare-datatypes
  ((eo.Term 0) (vsm.Value 0) (msm.Map 0) (ssm.Seq 0) (sm.Term 0) (tsm.Type 0) (dt.Datatype 0) (dtc.DatatypeCons 0))
  (
  (
$SM_EO_TERM_DECL$
  )
  (
$SM_VALUE_DECL$
  )
  (
$SM_MAP_DECL$
  )
  (
$SM_SEQ_DECL$
  )
  (
$SM_TERM_DECL$
  )
  (
$SM_TYPE_DECL$
  )
  (
  (dt.null)
  (dt.sum (dt.sum.arg1 dtc.DatatypeCons) (dt.sum.arg2 dt.Datatype))
  )
  (
  (dtc.unit)
  (dtc.cons (dtc.cons.arg1 tsm.Type) (dtc.cons.arg2 dtc.DatatypeCons))
  )
  )
)

(define-fun teq ((x eo.Term) (y eo.Term)) Bool (= x y))
(define-fun Teq ((x tsm.Type) (y tsm.Type)) Bool (= x y))
(define-fun veq ((x vsm.Value) (y vsm.Value)) Bool (= x y))

; forward declarations
(declare-fun texists (String tsm.Type sm.Term) vsm.Value)
(declare-fun tforall (String tsm.Type sm.Term) vsm.Value)
(declare-fun tchoice (String tsm.Type sm.Term) vsm.Value)
(declare-fun tlambda (String tsm.Type sm.Term) vsm.Value)
  
;;; Relevant definitions

$SM_DEFS$

;;; Meta-level properties of models

; axiom for hash
; note: this implies that $smtx_hash is injective, which implies $eo_hash is injective.
(assert (! (forall ((x eo.Term))
    (! (= ($eo_reverse_hash ($smtx_hash x)) x) :pattern (($smtx_hash x)))) :named eo.hash_injective))
(assert (! (forall ((x vsm.Value))
    (! (= ($smtx_reverse_value_hash ($smtx_value_hash x)) x) :pattern (($smtx_value_hash x)))) :named smtx.hash_injective))

; true iff there exists a value of type T that when substituted into F
; is evaluated as tgt. Note that we do not check the type of T here,
; instead $smtx_substitute will generate terms ($sm_Const v T), which
; only evaluate to v if it is of type T.
(define-fun texists_total ((s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (exists ((v vsm.Value))
    (= ($smtx_model_eval ($smtx_substitute s T ($mk_sm_const v T) F)) tgt)))

; true iff all values of type T when substituted into F are evaluated as tgt.
(define-fun tforall_total ((s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (forall ((v vsm.Value))
    (= ($smtx_model_eval ($smtx_substitute s T ($mk_sm_const v T) F)) tgt)))

; exists
(assert (forall ((s String) (T tsm.Type) (F sm.Term))
  (= (texists s T F)
     (ite (texists_total s T F ($mk_vsm_bool true)) ($mk_vsm_bool true)
     (ite (tforall_total s T F ($mk_vsm_bool false)) ($mk_vsm_bool false)
       vsm.NotValue)))))
  
; forall
(assert (forall ((s String) (T tsm.Type) (F sm.Term))
  (= (tforall s T F)
     (ite (texists_total s T F ($mk_vsm_bool false)) ($mk_vsm_bool false)
     (ite (tforall_total s T F ($mk_vsm_bool true)) ($mk_vsm_bool true)
       vsm.NotValue)))))

; choice
; If there exists a value making the existential true, we can assume
; that substituting with choice also makes it true.
(assert (forall ((s String) (T tsm.Type) (F sm.Term) (v vsm.Value))
  (=> (texists_total s T F ($mk_vsm_bool true))
      (= ($smtx_model_eval ($smtx_substitute s T ($mk_sm_const (tchoice s T F) T) F))
         ($mk_vsm_bool true)))))

;;; The verification condition

$SMT_VC$
