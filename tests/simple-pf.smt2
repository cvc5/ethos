
(declare-const = (-> (! Type :var T) T T Bool))


(declare-rule eq-symm ((T Type) (x T) (y T))
  :premises ((= T x y))
  :args ()
  :conclusion (= T y x))

  
(declare-sort Int 0)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Bool)
(assume a1 (= Int a b))
(step a2 (= Int b a) :rule eq-symm :premises (a1) :args ())
(proof (= Int b a) a2)
