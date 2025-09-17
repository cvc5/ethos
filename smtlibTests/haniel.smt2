(set-option :produce-proofs true)
;(set-option :proof-format-mode alethe)
;(set-option :proof-format-mode alf)

;(set-option :proof-granularity theory-rewrite)
(set-option :simplification none)

(set-logic QF_UF)

(declare-sort $U 0)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)

(declare-const a $U)
(declare-const b $U)
(declare-const c $U)
(declare-const d $U)
(declare-fun fun ($U $U) $U)

(assert (= a b))
(assert (= c d))
(assert (and p1 true))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (not (= (fun a c) (fun b d)))))

(check-sat)
;(get-proof)
