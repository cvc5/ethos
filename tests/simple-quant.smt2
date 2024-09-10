; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(assert (forall ((x Int)) (< x x)))
(check-sat)
