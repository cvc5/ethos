(set-logic ALL)
(declare-fun P (Int Int Int) Bool)

(assert (forall ((x Int) (y Int) (z Int)) (P x y z)))

(assert (exists ((x Int) (y Int)) (not (P x y 5))))

(check-sat)
