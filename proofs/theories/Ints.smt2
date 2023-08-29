(include "../theories/Arith.smt2")

; integer specific operators

(declare-consts <numeral> Int)

; Note: we do not have a left-neutral element for div.
(declare-const div (-> Int Int Int) :left-assoc)
(declare-const div_total (-> Int Int Int) :left-assoc)

(declare-const mod (-> Int Int Int))
(declare-const mod_total (-> Int Int Int))

(declare-const divisible (-> Int Int Bool))
