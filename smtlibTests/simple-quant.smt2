
(set-logic ALL)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (P x)))
(assert (not (P 5)))
(check-sat)
