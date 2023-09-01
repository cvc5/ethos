(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-const + (-> Int Int Int))
(declare-const - (-> Int Int Int))
(declare-const = (-> Int Int Bool))

(program check_pos ((x Int))
  (Int) Bool
  (
    ((check_pos x) (alf.ite (alf.is_neg x) (- x 1) (+ x 1)))
  )
)

(program check_sign ((x Int))
  (Int) Bool
  (
    ((check_sign x) (alf.ite (alf.is_zero x) x (alf.ite (alf.is_neg x) (- x 1) (+ x 1))))
  )
)

(program factorial ((x Int))
  (Int) Bool
  (
    ((factorial x) (alf.ite (alf.is_zero x) 1 (alf.mul x (factorial (alf.add x (alf.neg 1))))))
  )
)

(declare-fun f (Int) Int)


(declare-rule eval_factorial ((x Int))
  :args (x)
  :conclusion (= (f x) (factorial x)))
  
(step @p0 (= (f 4) 24) :rule eval_factorial :args (4))


(declare-fun e (Int) Int)

(declare-rule eval_check_sign ((x Int))
  :args (x)
  :conclusion (= (e x) (check_sign x)))
  
(step @p1 (= (e 2) (+ 2 1)) :rule eval_check_sign :args (2))
