; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(define-fun-rec f ((y Int)) Int (f y))
(assert (> (f x) 0))
(check-sat)
