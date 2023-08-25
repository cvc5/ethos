(set-option :produce-proofs true)
;(set-option :proof-format-mode alethe)
(set-option :proof-format-mode alethelf)

(set-option :proof-granularity theory-rewrite)

(set-logic QF_UF)

(declare-sort S 0)
(declare-const c S)

(assert (not (= c c)))

(check-sat)
(get-proof)
