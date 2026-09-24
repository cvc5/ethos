; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
; Repeating an assertion in a nested scope must not remove the outer copy.
(assert (> x 0))
(push)
(declare-fun y () Int)
(assert (> x 0))
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(pop)
(check-sat)
