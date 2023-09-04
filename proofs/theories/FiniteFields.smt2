(include "../theories/Arith.smt2")

(declare-const FiniteField (-> Int Type))

; A finite field constant is a term having 2 integer children.
; TODO: native syntax?
(declare-const ff.value
    (-> (! Int :var p) Int (FiniteField p)))

(declare-const ff.add
    (-> (! Int :var p :implicit)
        (FiniteField p) (FiniteField p) (FiniteField p)) :right-assoc-nil
)
(declare-const ff.neg
    (-> (! Int :var p :implicit)
        (FiniteField p) (FiniteField p))
)
(declare-const ff.mul
    (-> (! Int :var p :implicit)
        (FiniteField p) (FiniteField p) (FiniteField p)) :right-assoc-nil
)
