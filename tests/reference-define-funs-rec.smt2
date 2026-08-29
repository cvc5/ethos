; not a regression, to be used by reference commands
(set-logic ALL)
(declare-fun x () Int)
(define-funs-rec ((f ((y Int)) Int) (g ((y Int)) Int)) ((g y) (f y)))
(assert (> (f x) 0))
(check-sat)
