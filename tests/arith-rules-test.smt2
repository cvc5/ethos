(include "../proofs/rules/Arith.smt2")

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)

(assume @p0 (< x (* 2 y)))
(assume @p1 (< y z))
(assume @p2 (<= w 0))


(step @p3 :rule arith_sum_ub :premises (@p0 @p1 @p2))
(step @p4 :rule arith_mult_pos :args ((> y z) 4))
(step @p5 :rule arith_mult_neg :args ((> y z) (alf.neg 4)))
