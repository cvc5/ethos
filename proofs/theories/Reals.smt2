(include "./proofs/theories/Core.smt2")
(include "./proofs/theories/ArithBridge.smt2")

(declare-consts <decimal> Real)

;(declare-const - (-> Real Real))
(declare-const + (-> Real Real Real))
(declare-const * (-> Real Real Real))
(declare-const <= (-> Real Real Bool))
(declare-const is_int (-> Real Bool))

(declare-const - (-> Real Real Real))
(declare-const / (-> Real Real Real))
(declare-const < (-> Real Real Bool)) 
(declare-const > (-> Real Real Bool))
(declare-const >= (-> Real Real Bool))
(declare-const sum (-> Real Real (-> Real Real) Real))
