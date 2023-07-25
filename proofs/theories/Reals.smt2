(include "../theories/Core.smt2")
(include "../theories/ArithBridge.smt2")

(declare-consts <decimal> Real)

; TODO: needs overloading
;(declare-const - (-> Real Real))
(declare-const + (-> Real Real Real)
    :left-assoc 0
)
(declare-const * (-> Real Real Real)
    :left-assoc 1
)
(declare-const <= (-> Real Real Bool)
    :chainable and
)
(declare-const is_int (-> Real Bool))

(declare-const - (-> Real Real Real)
    :left-assoc
)
(declare-const / (-> Real Real Real))
(declare-const < (-> Real Real Bool)) 
(declare-const > (-> Real Real Bool))
(declare-const >= (-> Real Real Bool))
(declare-const sum (-> Real Real (-> Real Real) Real))
