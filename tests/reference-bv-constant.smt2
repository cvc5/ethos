; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () (BitVec 8))
(declare-fun y () (BitVec 4))
(assert (= x (_ bv5 8)))
(assert (= y (_ bv10 4)))
(check-sat)
