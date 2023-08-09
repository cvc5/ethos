
(declare-const = (-> (! Type :var T) T T Bool))

;(declare-const = ((T Type)) (-> T T Bool))

(declare-const not (-> Bool Bool))

(declare-rule eq-symm-taut ((T Type) (x T) (y T))
  :premises ()
  :args ((= T x y))
  :conclusion (= Bool (= T x y) (= T y x)))
  

(declare-sort Int 0)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun c () Bool)
(step a5 (= Bool (= Int x y) (= Int y x)) :rule eq-symm-taut :premises () :args ((= Int x y)))
;(step a6 (= Bool (= Int x y) (= Int y x)) :rule eq-symm-taut :premises () :args (x))

(proof (= Bool (= Int x y) (= Int y x)) a5)
