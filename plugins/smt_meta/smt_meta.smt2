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
  (dt.unit (dt.unit.arg1 dtc.DatatypeCons))
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
(declare-fun $smtx_model_eval_exists (String tsm.Type sm.Term) vsm.Value)
(declare-fun $smtx_model_eval_forall (String tsm.Type sm.Term) vsm.Value)
(declare-fun $smtx_model_eval_lambda (String tsm.Type sm.Term) vsm.Value)
  
;;; Relevant definitions

$SM_DEFS$

;;; Meta-level properties of models

; axiom for hash
; note: this implies that $smtx_hash is injective, which implies $eo_hash is injective.
(assert (! (forall ((x eo.Term))
    (! (= ($eo_reverse_hash ($smtx_hash x)) x) :pattern (($smtx_hash x)))) :named eo.hash_injective))
(assert (! (forall ((x vsm.Value))
    (! (= ($smtx_reverse_value_hash ($smtx_value_hash x)) x) :pattern (($smtx_value_hash x)))) :named smtx.hash_injective))

(define-fun texists ((s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (exists ((v vsm.Value))
    (and (= ($smtx_typeof_value v) T)
         (= ($smtx_model_eval ($smtx_substitute s T v F)) tgt))))

(define-fun tforall ((s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (forall ((v vsm.Value))
    (=> (= ($smtx_typeof_value v) T)
        (= ($smtx_model_eval ($smtx_substitute s T v F)) tgt))))

; exists
(assert (forall ((s String) (T tsm.Type) (F sm.Term))
  (= ($smtx_model_eval_exists s T F)
     (ite (texists s T F ($mk_vsm_bool true)) ($mk_vsm_bool true)
     (ite (tforall s T F ($mk_vsm_bool false)) ($mk_vsm_bool false)
       vsm.NotValue)))))
  
; forall
(assert (forall ((s String) (T tsm.Type) (F sm.Term))
  (= ($smtx_model_eval_exists s T F)
     (ite (texists s T F ($mk_vsm_bool false)) ($mk_vsm_bool false)
     (ite (tforall s T F ($mk_vsm_bool true)) ($mk_vsm_bool true)
       vsm.NotValue)))))

;;; The verification condition

$SMT_VC$
