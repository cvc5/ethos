(declare-sort Pair 1)

(declare-const pair (-> (! Type :var T :implicit) T T (Pair T)))


(program swap ((T Type) (t1 T) (t2 T))
  ((Pair T)) (Pair T)
  ; cases
  (
  ((swap (pair t1 t2)) (pair t2 t1))
  )
)

(declare-const is_swap (-> (! Type :var T :implicit) (Pair T) (Pair T) Bool))

(declare-rule do_swap ((T Type) (t (Pair T)))
  :premises ()
  :args (t)
  :conclusion (is_swap t (swap t))
)

(declare-sort Int 0)
(declare-const a Int)
(declare-const b Int)

(step a0 (is_swap (pair a b) (pair b a)) :rule do_swap :premises () :args ((pair a b)))
