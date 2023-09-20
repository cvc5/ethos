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
(declare-const < (-> (! Type :var T :implicit) 
                      T T Bool))
(declare-const <= (-> (! Type :var T :implicit) 
                      T T Bool))


(program run_evaluate ((T Type) (U Type) (S Type) (a T) (b U) (z S))
    (S) S
    (
      ((run_evaluate (= a b))  (alf.is_eq (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (< a b))  (alf.is_neg (run_evaluate (- a b))))
      ((run_evaluate (<= a b)) (let ((x (run_evaluate (- a b)))) 
                                 (alf.or (alf.is_neg x) (alf.is_zero x))))
      ((run_evaluate (+ a b))  (alf.add (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (- a b))  (alf.add (run_evaluate a) (alf.neg (run_evaluate b))))
      ((run_evaluate z)        z)
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
(step a2 (= (- 0.6 0.2) 0.4) :rule eval :args ((- 0.6 0.2) 0.4))
(step a3 (= (< 1.25 1.5) true) :rule eval :args ((< 1.25 1.5) true))
(step a4 (= (<= 1.25 1.5) true) :rule eval :args ((<= 1.25 1.5) true))
; should be agnostic to spurious zeroes
(step a5 (= (= 1.500 1.5) true) :rule eval :args ((= 1.5000 1.5) true))
