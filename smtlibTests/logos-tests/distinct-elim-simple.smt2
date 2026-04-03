(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

(assert (distinct a b c))
(assert (or (= a b) (= b c)))
(check-sat)
