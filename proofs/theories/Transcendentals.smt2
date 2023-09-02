(include "../theories/Arith.smt2")

; transcendental-specific operators


(declare-const real.pi Real)
(declare-const exp (-> Real Real))
(declare-const sin (-> Real Real))
(declare-const cos (-> Real Real))
(declare-const tan (-> Real Real))
(declare-const csc (-> Real Real))
(declare-const sec (-> Real Real))
(declare-const cot (-> Real Real))
(declare-const arcsin (-> Real Real))
(declare-const arccos (-> Real Real))
(declare-const arctan (-> Real Real))
(declare-const arccsc (-> Real Real))
(declare-const arcsec (-> Real Real))
(declare-const arccot (-> Real Real))
(declare-const sqrt (-> Real Real))

;SQRT
;TRANSCENDENTAL_PURIFY_ARG
