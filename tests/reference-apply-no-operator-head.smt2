; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(assert ((_) x))
(check-sat)
