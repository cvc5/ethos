; depends: arith_programs.plf

(include "../theories/Core.smt2")
(include "../theories/Arith.smt2")
(include "../programs/Arith.smt2")


(program mk_arith_sum_ub_step
  ((T Type) (U Type) (S Type) (V Type) (r1 (-> T U Bool)) (a1 T) (b1 U) (r2 (-> S V Bool)) (a2 S :list) (b2 V :list))
  (Bool Bool) Bool
  (
    ((mk_arith_sum_ub_step (r1 a1 b1) (r2 a2 b2)) (_ (arith_rel_sum r1 r2) (+ a1 a2) (+ b1 b2)))
  )
)

(program mk_arith_sum_ub ((T Type) (U Type) (r (-> T U Bool)) (a T) (b U) (tail Bool :list))
    (Bool Bool) Bool
    (
        ((mk_arith_sum_ub (alf.nil Bool)) (= 0 0))
        ((mk_arith_sum_ub (and (r a b) tail)) (mk_arith_sum_ub_step (r a b) (mk_arith_sum_ub tail)))
    )
)

(declare-rule arith_sum_ub ((F Bool))
  :premise-list F and
  :conclusion (mk_arith_sum_ub F)
)

; Computes the conclusion of the PfRule::ARITH_MULT_POS rule.
(program mk_arith_mult_pos ((T Type) (U Type) (S Type) (r (-> T U Bool)) (a T) (b U) (m S))
  (Bool S) Bool
  (
    ((mk_arith_mult_pos (r a b) m) (r (* m a) (* m b)))
  )
)

(declare-rule arith_mult_pos ((T Type) (m T) (F Bool))
  :args (m F)
  :conclusion (=> (and (> m 0) F) (mk_arith_mult_pos F m))
)

; Computes the conclusion of the PfRule::ARITH_MULT_NEG rule.
(program mk_arith_mult_neg ((T Type) (U Type) (S Type) (r (-> T U Bool)) (a T) (b U) (m S))
  (Bool S) Bool
  (
    ((mk_arith_mult_neg (r a b) m) (_ (arith_rel_inv r) (* m a) (* m b)))
  )
)

(declare-rule arith_mult_neg ((T Type) (m T) (F Bool))
  :args (m F)
  :conclusion (=> (and (< m 0) F) (mk_arith_mult_neg F m))
)


; Computes the conclusion of the PfRule::ARITH_TRICHOTOMY rule.
(program mk_arith_trichotomy ((T Type) (U Type) (S Type) (r1 (-> T U Bool)) (r2 (-> T U Bool)) (a T) (b U) (m S))
  (Bool S) Bool
  (
    ((mk_arith_trichotomy (r1 a b) (r2 a b)) (_ (arith_rel_trichotomy r1 r2) a b))
  )
)

(declare-rule arith_trichotomy ((F1 Bool) (F2 Bool))
  :premises (F1 F2)
  :conclusion (mk_arith_trichotomy (arith_normalize_lit F1) (arith_normalize_lit F2))
)

; Returns true if c is the greatest integer less than (integer or real) constant
; t. We compute this via conditions 0 <= c-t ^ (c-t)-1 <= 0.
(program check_int_tight_ub ((t Int) (c Int))
  (Int Int) Bool
  (
    ((check_int_tight_ub t c) true)
  )
)

(declare-rule int_tight_ub ((s Int) (t Real) (c Int))
  :premises ((< s t))
  :args (c)
  :requires (((check_int_tight_ub t c) true))
  :conclusion (<= s c)
)

; Returns true if c2 is the least integer greater than c1. We compute this
; via conditions 0 <= c1-c2 ^ (c1-c2)-1 <= 0.
(program check_int_tight_lb ((t Int) (c Int))
  (Int Int) Bool
  (
    ((check_int_tight_lb t c) true)
  )
)

(declare-rule int_tight_lb ((s Int) (t Real) (c Int))
  :premises ((> s t))
  :args (c)
  :requires (((check_int_tight_lb t c) true))
  :conclusion (>= s c)
)
