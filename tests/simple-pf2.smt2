
(declare-const = (-> (! Type :var T) T T Bool))

(declare-const false Bool)
(declare-const not (-> Bool Bool))

(declare-rule eq-symm ((T Type) (x T) (y T))
  :premises ((= T x y))
  :args ()
  :conclusion (= T y x))
  
(declare-rule contra ((p Bool))
  :premises (p (not p))
  :args ()
  :conclusion false
)

(declare-sort Int 0)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun c () Bool)
(assume a1 (= Int x y))
(assume a2 (not (= Int y x)))
(step a3 (= Int y x) :rule eq-symm :premises (a1) :args ())
(step a4 false :rule contra :premises (a3 a2) :args ())
(proof false a4)
