
(declare-const = (-> (! Type :var T :implicit) T T Bool))


(declare-rule eq-symm ((T Type) (x T) (y T))
  :premises ((= x y))
  :args ()
  :conclusion (= y x))

  
(declare-sort Int 0)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Bool)
(assume a1 (= a b))
(step a2 (= b a) :rule eq-symm :premises (a1) :args ())
(proof (= b a) a2)
