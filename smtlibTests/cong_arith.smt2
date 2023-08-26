(set-option :produce-proofs true)
;(set-option :proof-format-mode alethe)
(set-option :proof-format-mode alf)
(set-option :dag-thresh 0)

(set-option :proof-granularity theory-rewrite)

(set-logic QF_UFLIA)

(declare-fun P (Int Int Int) Bool)

(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)
(declare-const c4 Int)
(declare-const c5 Int)
(declare-const c6 Int)

(assert (= c1 c2))
(assert (= c3 c4))
(assert (= c5 c6))
(assert (P c1 c3 c5))
(assert (not (P c2 c4 c6)))

(check-sat)
(get-proof)
