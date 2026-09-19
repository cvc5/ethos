(set-option :produce-proofs true)
;(set-option :proof-format-mode alethe)
(set-option :proof-format-mode alf)
(set-option :dag-thresh 0)

(set-option :proof-granularity theory-rewrite)

(set-logic QF_UF)

(declare-sort S 0)

(declare-fun P (S S) Bool)

(declare-const c1 S)
(declare-const c2 S)
(declare-const c3 S)
(declare-const c4 S)

(assert (= c1 c2))
(assert (P c1 c4))
(assert (not (P c2 c4)))

(check-sat)
;(get-proof)
