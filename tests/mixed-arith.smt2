(declare-sort Int 0)
(declare-sort Real 0)

(declare-consts <numeral> Int)
(declare-consts <decimal> Real)


(declare-const = (-> (! Type :var T :implicit) T T Bool))

(program a.typeunion ()
    (Type Type) Type
    (
      ((a.typeunion Int Int) Int)
      ((a.typeunion Int Real) Real)
      ((a.typeunion Real Int) Real)
      ((a.typeunion Real Real) Real)
    )
)

(declare-const + (-> (! Type :var T :implicit) 
                     (! Type :var U :implicit) 
                     T U (a.typeunion T U)))
(declare-const - (-> (! Type :var T :implicit) 
                     (! Type :var U :implicit) 
                     T U (a.typeunion T U)))


(program run_evaluate ((T Type) (U Type) (S Type) (a T) (b U) (z S))
    (S) S
    (
      ((run_evaluate (+ a b)) (eval.add (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (- a b)) (eval.add (run_evaluate a) (eval.neg (run_evaluate b))))
      ((run_evaluate z)       z)
    )
)

(declare-rule eval
   ((T Type) (U Type) (a T) (b U))
   :premises ()
   :args (a b)
   :requires (((run_evaluate a) (run_evaluate b)))
   :conclusion (= a b)
)


(step a1 (= (+ 0.5 0.25) 0.75) :rule eval :args ((+ 0.5 0.25) 0.75))
(step a2 (= (- 0.5 0.25) 0.25) :rule eval :args ((- 0.5 0.25) 0.25))
