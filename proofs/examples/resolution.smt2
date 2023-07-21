(include "./proofs/rules/Booleans.smt2")

(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const c3 Bool)

(assume a1 (or      c1  c2))
(assume a2 (or (not c2) c3))
(assume a3 (not c2))

(step t1 (or c1 c3) :rule resolution :premises (a1 a2) :args (true c2))
;(step t2 (or c3 c1) :rule resolution :premises (a2 a1) :args (false c2))

;(step t3 c1 :rule resolution :premises (a1 a3) :args (true c2))

