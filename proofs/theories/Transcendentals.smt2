(include "../theories/Arith.smt2")

; transcendental-specific operators


(declare-const real.pi Real)
(declare-const exp (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const sin (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const cos (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const tan (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const csc (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const sec (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const cot (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const arcsin (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const arccos (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const arctan (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const arccsc (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const arcsec (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const arccot (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))
(declare-const sqrt (-> (! Type :var T :implicit) T (! Real :requires ((is_arith_type T) true))))

; skolems
(declare-const @k.SQRT (-> Real Real))
(declare-const @k.TRANSCENDENTAL_PURIFY_ARG (-> Real Real))
