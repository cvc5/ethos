
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

; The constant predicate holds for the model value of a constant.
(assert (! (forall ((T tsm.Type) (k sm.Term) (i Int))
  ($smtx_const_predicate T k i))
 :named sm.model_is_value))

;;; The verification condition

$SMT_VC$

(check-sat)
