
;;; Utilities

; Stuckness propagates through non-nullary constructors
(define-fun $eo_FunType ((x eo.Term) (y eo.Term)) eo.Term
  (ite (or (= x eo.Stuck) (= y eo.Stuck))
    eo.Stuck
    (eo.FunType x y)))

(define-fun $eo_Apply ((x eo.Term) (y eo.Term)) eo.Term
  (ite (or (= x eo.Stuck) (= y eo.Stuck))
    eo.Stuck
    (eo.Apply x y)))

;;; Core operators

; Note that these cannot be lifted further since their semantics wrt
; stuckness is non-standard.
; TODO: maybe better if these are lifted and made a special case?

; axiom: $eo_requires
(define-fun $eo_requires ((x1 eo.Term) (x2 eo.Term) (x3 eo.Term)) eo.Term
  (ite (and (not (= x1 eo.Stuck)) (not (= x2 eo.Stuck)) (= x1 x2))
    x3
    eo.Stuck))

;;; User defined symbols

$SM_DEFS$

;;; Meta-level properties of models

; axiom: $eo_hash
; note: This is defined axiomatically.
(assert (! (forall ((x eo.Term))
  (=> (not (= x eo.Stuck))
    (and
      ((_ is eo.SmtTerm) ($eo_hash x))
      ((_ is sm.Numeral) (eo.SmtTerm.arg1 ($eo_hash x)))))) :named sm.hash_numeral))
(assert (! (forall ((x eo.Term) (y eo.Term))
  (=> (and (not (= x eo.Stuck)) (not (= y eo.Stuck))
    (= ($eo_hash x) ($eo_hash y))) (= x y))) :named sm.hash_injective))

; Handles free constants, skolems, and TODO: partial functions.
; If the constant predicate for a constant is satisfied,
; then we may assume that the model value for that constant is a value.
(assert (! (forall ((k Int) (i Int) (T tsm.Type))
  (=> (or
        ; free constants always can be assumed to be a value
        (= i 0)
        ; skolems can be assumed to be a value if their predicate is satisfied
        ($smtx_const_predicate k i T ($smtx_model_lookup k i T)))
      ($smtx_is_value T ($smtx_model_lookup k i T))))
 :named sm.model_is_value))

;;; The verification condition

$SMT_VC$

(check-sat)
