; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(assert (> ((_ opq 5) x) 0))
(assert (> ((_ opq2 7 9) x) 0))
(check-sat)
