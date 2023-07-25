(include "../theories/Core.smt2")
(include "../theories/ArithBridge.smt2")

; 0, 1, 2, ...
(declare-consts <numeral> Int) 
; successor
(declare-const +1 (-> Int Int))
; predecessor
(declare-const -1 (-> Int Int))

(declare-const < (-> Int Int Bool)
    :chainable and
)
(declare-const <= (-> Int Int Bool)
    :chainable and
)
(declare-const > (-> Int Int Bool)
    :chainable and
)
(declare-const >= (-> Int Int Bool)
    :chainable and
)
; TODO: needs overloading
;(declare-const - (-> Int Int))
(declare-const + (-> Int Int Int)
    :left-assoc 0
)
; Note: we do not have a left-neutral element for -.
(declare-const - (-> Int Int Int)
    :left-assoc
)
(declare-const * (-> Int Int Int)
    :left-assoc 1
)
(declare-const abs (-> Int Int))
; Note: we do not have a left-neutral element for div.
(declare-const div (-> Int (! Int :var n) Int)
    :left-assoc
)
(declare-const mod (-> Int Int Int))
(declare-const divisible (-> Int (! Int :var n) Bool))
(declare-const sum (-> Int Int (-> Int Int) Int))
