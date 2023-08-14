(include "./quant.smt2")

(declare-sort Int 0)

(declare-var x1 Int)
(declare-const a Int)

(step x_eq_x (= x1 x1) :rule refl :args (x1))

(step forall_x_eq_x (forall x1 (= x1 x1)) :rule forall-intro :premises (x_eq_x) :args (x1))


(step inst (=> (forall x1 (= x1 x1)) (= a a)) :rule forall-inst :premises (forall_x_eq_x) :args (a))
