(include "../theories/Arith.smt2")

; integer specific operators

; Note: we do not have a left-neutral element for div.
(declare-const div (-> Int Int Int) :left-assoc)
(declare-const div_total (-> Int Int Int) :left-assoc)

(declare-const mod (-> Int Int Int))
(declare-const mod_total (-> Int Int Int))

(declare-const divisible (-> Int Int Bool))

; "integer-and", see Zohar et al VMCAI 2022.
(declare-const iand (-> Int Int Int Int))
(declare-const int.pow2 (-> Int Int))

; skolems
(declare-const @k.INT_DIV_BY_ZERO (-> Int Int))
(declare-const @k.MOD_BY_ZERO (-> Int Int))
