(declare-const true Bool)
(declare-const false Bool)

(declare-const or (-> Bool Bool Bool) :left-assoc false)
(declare-const and (-> Bool Bool Bool) :right-assoc true)
(declare-const not (-> Bool Bool))
(declare-const = (-> (! Type :var T :implicit) T T Bool))


(program substitute
  ((T Type) (U Type) (S Type) (x S) (y S) (f (-> T U)) (a T) (z U))
  (S S U) U
  (
  ((substitute x y x)     y)
  ((substitute x y (f a)) (@ (substitute x y f) (substitute x y a)))
  ((substitute x y z)     z)
  )
)


(declare-rule eq-subs
   ((f Bool) (a Bool) (b Bool))
   :premises (f (= a b))
   :args ()
   :conclusion (substitute a b f)
)

(declare-const a Bool)
(declare-const b Bool)
(assume a1 (or a b b (and (not a) a) b))
(assume a2 (= a b))
(step a3 (or b b b (and (not b) b) b) :rule eq-subs :premises (a1 a2))
