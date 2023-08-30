(include "../theories/Arith.smt2")

; real-specific operators

(declare-const / (-> (! Type :var T :requires ((is_arith_type T) true))
                     (! Type :var U :requires ((is_arith_type U) true))
                     Real) :left-assoc)

(declare-const /_total (-> (! Type :var T :requires ((is_arith_type T) true))
                           (! Type :var U :requires ((is_arith_type U) true))
                           Real) :left-assoc)
