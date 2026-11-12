(set-option :produce-proofs true)
;(set-option :proof-format-mode alethe)
(set-option :proof-format-mode alethelf)

(set-option :proof-granularity theory-rewrite)

(set-logic QF_UF)

(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const c3 Bool)
(declare-const c4 Bool)

(assert (= c1 c2))
(assert (not c1))
(assert (or c1 c3))
(assert (=> c3 c4))
(assert (not c4))

(check-sat)
(get-proof)
