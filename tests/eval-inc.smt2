(declare-sort Int 0)

(declare-consts <numeral> Int)

(declare-const = (-> (! Type :var T :implicit) T T Bool))

(declare-const + (-> Int Int Int))

(program run_inc ((a Int))
    (Int) Int
    (
      ((run_inc a) (alf.add 1 a))
    )
)

(declare-rule inc
   ((a Int))
   :premises ()
   :args (a)
   :conclusion (= (+ a (alf.add 0 1)) (run_inc a))
)


(step a1 (= (+ 4 1) 5) :rule inc :args (4))
