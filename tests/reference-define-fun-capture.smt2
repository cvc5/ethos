; regression for issue #279: a definition whose body binds a variable that its
; uses are applied to
(set-logic ALL)
(define-fun P ((y Int)) Bool (forall ((x Int)) (= x y)))
(assert (forall ((x Int)) (P x)))
(check-sat)
