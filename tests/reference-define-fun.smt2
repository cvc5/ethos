; a reference file with a define-fun with arguments
(set-logic ALL)
(declare-fun x () Int)
(define-fun gt0 ((y Int)) Bool (> y 0))
(assert (gt0 x))
(check-sat)
