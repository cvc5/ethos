(define-fun f ((x Int)) Bool false)
(define-fun g ((x Int)) Bool true)
(assert (f 0))
(check-sat)
