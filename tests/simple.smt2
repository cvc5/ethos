; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(assert (< x 0))
(assert (> x 0))
(check-sat)
