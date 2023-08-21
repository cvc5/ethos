(declare-sort Int 0)
(declare-consts <numeral> Int)

(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const + (-> Int Int Int))
(declare-const - (-> Int Int Int))
(declare-const < (-> Int Int Bool))
(declare-const <= (-> Int Int Bool))

(program arith.eval ((S Type) (a Int) (b Int) (z S))
    (S) S
    (
      ((arith.eval (= a b))  (alf.is_eq (arith.eval a) (arith.eval b)))
      ((arith.eval (< a b))  (alf.is_neg (arith.eval (- a b))))
      ((arith.eval (<= a b)) (let ((x (arith.eval (- a b)))) 
                                 (alf.or (alf.is_neg x) (alf.is_zero x))))
      ((arith.eval (+ a b))  (alf.add (arith.eval a) (arith.eval b)))
      ((arith.eval (- a b))  (alf.add (arith.eval a) (alf.neg (arith.eval b))))
      ((arith.eval z)        z)
    )
)

(declare-sort String 0)
(declare-consts <string> String)
  
(declare-const str.++ (-> String String String))
(declare-const str.len (-> String Int))
(declare-const str.substr (-> String Int Int String))

(program str.eval ((S Type) (a String) (b String) (z S) (n Int) (m Int))
    (S) S
    (
      ((str.eval (= a b))            (alf.is_eq (str.eval a) (str.eval b)))
      ((str.eval (str.++ a b))       (alf.concat (str.eval a) (str.eval b)))
      ((str.eval (str.len a))        (alf.len (str.eval a)))
      ((str.eval (str.substr a n m)) (alf.extract (arith.eval n) (arith.eval (+ n m)) (str.eval a)))
      ((str.eval z)                  z)
    )
)

(declare-rule eval
   ((T Type) (U Type) (a T) (b U))
   :premises ()
   :args (a b)
   :requires (((str.eval a) (str.eval b)))
   :conclusion (= a b)
)

(declare-const x String)

(step a2 (= 4 (str.len "ABCD")) :rule eval :premises (4 (str.len "ABCD")))
(step a3 (= 1 (str.len "\u{45}")) :rule eval :premises (1 (str.len "\u{45}")))
(step a4 (= "B" (str.substr (str.++ "A" "BC") 1 1)) :rule eval :premises ("B" (str.substr (str.++ "A" "BC") 1 1)))
(step a5 (= 9 (str.len "\u{45}\uu{\u1A11\u0")) :rule eval :premises (9 (str.len "\u{45}\uu{\u1A11\u0")))
