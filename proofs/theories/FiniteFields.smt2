(include "../theories/Arith.smt2")

(declare-const FiniteField (-> Int Type))

; A finite field constant is a term having 2 integer children.
;(declare-const f_ff.value term)

(declare-const ff.add
    (-> (! Int :var p :implicit)
        (FiniteField p) (FiniteField p) (FiniteField p))
)
(declare-const ff.neg
    (-> (! Int :var p :implicit)
        (FiniteField p) (FiniteField p))
)
(declare-const ff.mul
    (-> (! Int :var p :implicit)
        (FiniteField p) (FiniteField p) (FiniteField p))
)
