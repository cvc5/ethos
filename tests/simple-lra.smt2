; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Real)
(assert (< x 0))
(assert (< 1 x))
(check-sat)
