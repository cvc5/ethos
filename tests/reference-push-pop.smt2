; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(assert (> x 0))
(check-sat)
