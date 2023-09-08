
(include "./simple-sig.smt2")

(declare-sort Int 0)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Bool)
(assume a1 (= a b))
(assume a2 (not (= b a)))
(step a3 (= b a) :rule eq-symm :premises (a1) :args ())
(step a31 (= b a) :rule eq-symm-flip :premises (a1) :args ((= b a)))
(step a4 false :rule contra :premises (a3 a2) :args ())
