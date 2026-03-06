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

; integer exponentiation is not handled by cvc5, axiomatize it
(declare-fun zexp_total (Int Int) Int)
(assert (forall ((x Int) (y Int)) (= (zexp_total x y) (ite (< y 0) 0 (ite (= y 0) 1 (* x (zexp_total x (- y 1))))))))

(define-fun bit ((x1 Int) (x2 Int)) Bool
  (zeq 1 (mod (div x1 (int.pow2 x2)) 2)))
(define-fun msb ((x1 Int) (x2 Int)) Bool
  (bit x2 (zplus x1 (zneg 1))))
(define-fun binary_and ((x1 Int) (x2 Int) (x3 Int)) Int
  (ite (zeq x1 0) 0 (piand x1 x2 x3)))
(define-fun binary_or ((x1 Int) (x2 Int) (x3 Int)) Int
  (zplus x2 (zplus x3 (zneg (ite (zeq x1 0) 0 (piand x1 x2 x3))))))
(define-fun binary_xor ((x1 Int) (x2 Int) (x3 Int)) Int
  (zplus x2 (zplus x3 (zneg (zmult 2 (ite (zeq x1 0) 0 (piand x1 x2 x3)))))))
(define-fun binary_not ((x1 Int) (x2 Int)) Int
  (zplus (int.pow2 x1) (zneg (zplus x2 1))))
(define-fun binary_max ((x1 Int)) Int
  (zplus (int.pow2 x1) (zneg 1)))
(define-fun binary_uts ((w Int) (n Int)) Int
  (zplus (zmult 2 (mod n (int.pow2 (zplus w (zneg 1))))) (zneg n)))
(define-fun binary_concat ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int
  (zplus (zmult x2 (int.pow2 x3)) x4))
(define-fun binary_extract ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int
  (div x2 (int.pow2 x4)))
    
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
  ((eo.Term 0)  (edt.Datatype 0) (edtc.DatatypeCons 0)
   (vsm.Value 0) (msm.Map 0) (ssm.Seq 0) (sm.Term 0) (tsm.Type 0)
   (dt.Datatype 0) (dtc.DatatypeCons 0))
  (
  (
$SM_EO_TERM_DECL$
  )
  (
  (edt.null)
  (edt.sum (edt.sum.arg1 edtc.DatatypeCons) (edt.sum.arg2 edt.Datatype))
  )
  (
  (edtc.unit)
  (edtc.cons (edtc.cons.arg1 eo.Term) (edtc.cons.arg2 edtc.DatatypeCons))
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

; models
(declare-sort smm.SmtModel 0)

(define-fun teq ((x eo.Term) (y eo.Term)) Bool (= x y))
(define-fun Teq ((x tsm.Type) (y tsm.Type)) Bool (= x y))
(define-fun veq ((x vsm.Value) (y vsm.Value)) Bool (= x y))

(declare-fun thash (eo.Term) Int)
(declare-fun trevhash (Int) eo.Term)
; axiom for hash
; note: this implies that thash is injective, which implies $eo_hash is injective.
(assert (! (forall ((x eo.Term))
    (! (= (trevhash (thash x)) x) :pattern ((thash x)))) :named eo.hash_injective))
(define-fun tcmp ((a eo.Term) (b eo.Term)) Bool (< (thash a) (thash b)))

; forward declarations
(declare-fun texists (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun tforall (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun tchoice (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun tlambda (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
  
;;; Relevant definitions

$SM_DEFS$

;;; Meta-level properties of models

; models are well typed
(assert (! (forall ((M smm.SmtModel) (id Int) (T tsm.Type))
              (= ($smtx_typeof_value ($smtx_model_lookup M id T)) T)) :named smtx.model_lookup_well_typed))

(assert (! (forall ((x vsm.Value))
    (! (= ($smtx_reverse_value_hash ($smtx_value_hash x)) x) :pattern (($smtx_value_hash x)))) :named smtx.hash_injective))

; true iff there exists a value of type T that when substituted into F
; is evaluated as tgt. Note that we do not check the type of T here,
; instead $smtx_substitute will generate terms ($sm_Const v T), which
; only evaluate to v if it is of type T.
(define-fun texists_total ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (exists ((v vsm.Value))
    (= ($smtx_model_eval M ($smtx_substitute s T (sm.Const v T) F)) tgt)))

; true iff all values of type T when substituted into F are evaluated as tgt.
(define-fun tforall_total ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (forall ((v vsm.Value))
    (= ($smtx_model_eval M ($smtx_substitute s T (sm.Const v T) F)) tgt)))

; exists
(assert (forall ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term))
  (= (texists M s T F)
     (ite (texists_total M s T F (vsm.Boolean true)) (vsm.Boolean true)
     (ite (tforall_total M s T F (vsm.Boolean false)) (vsm.Boolean false)
       vsm.NotValue)))))
  
; forall
(assert (forall ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term))
  (= (tforall M s T F)
     (ite (texists_total M s T F (vsm.Boolean false)) (vsm.Boolean false)
     (ite (tforall_total M s T F (vsm.Boolean true)) (vsm.Boolean true)
       vsm.NotValue)))))

; choice
; If there exists a value making the existential true, we can assume
; that substituting with choice also makes it true.
(assert (forall ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term) (v vsm.Value))
  (=> (texists_total M s T F (vsm.Boolean true))
      (= ($smtx_model_eval M ($smtx_substitute s T (sm.Const (tchoice M s T F) T) F))
         (vsm.Boolean true)))))

; whether two values are extensionally equal
; FIXME: 3 valued?
(define-fun t_ext_equal ((v1 vsm.Value) (v2 vsm.Value)) Bool
  (forall ((i vsm.Value)) (= ($smtx_model_eval_apply v1 i) ($smtx_model_eval_apply v2 i))))

;;; The verification condition

$SMT_VC$
