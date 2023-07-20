(include "./proofs/theories/Core.smt2")
(include "./proofs/theories/ArithBridge.smt2")

; 0, 1, 2, ...
(declare-consts <numeral> Int) 
; successor
(declare-const +1 (-> Int Int))
; predecessor
(declare-const -1 (-> Int Int))

(declare-const < (-> Int Int Bool))
(declare-const <= (-> Int Int Bool))
(declare-const > (-> Int Int Bool))
(declare-const >= (-> Int Int Bool))
;(declare-const - (-> Int Int))
(declare-const + (-> Int Int Int))
(declare-const - (-> Int Int Int))
(declare-const * (-> Int Int Int))
(declare-const abs (-> Int Int))
(declare-const div (-> Int (! Int :var n) Int))
(declare-const mod (-> Int Int Int))
(declare-const divisible (-> Int (! Int :var n) Bool))
(declare-const sum (-> Int Int (-> Int Int) Int))
