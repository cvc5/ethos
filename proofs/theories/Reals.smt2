(include "../theories/Core.smt2")
(include "../theories/ArithBridge.smt2")

(declare-consts <decimal> Real)

; TODO: needs overloading
;(declare-const - (-> Real Real))
(declare-const + (-> Real Real Real)
    :right-assoc-nil
)
(declare-const * (-> Real Real Real)
    :right-assoc-nil
)
(declare-const <= (-> Real Real Bool)
    :chainable and
)
(declare-const is_int (-> Real Bool))

(declare-const - (-> Real Real Real)
    :left-assoc
)
(declare-const / (-> Real Real Real)
    :left-assoc
)
(declare-const < (-> Real Real Bool)
    :chainable and
)
(declare-const > (-> Real Real Bool)
    :chainable and
)
(declare-const >= (-> Real Real Bool)
    :chainable and
)
(declare-const sum (-> Real Real (-> Real Real) Real))
