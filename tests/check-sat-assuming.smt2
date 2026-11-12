; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(assert (> x 0))
(check-sat-assuming ((< x 0) (< x 1)))
