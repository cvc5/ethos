(program maybe_nil ((T Type) (t T))
    (T T) T
    (
      ((maybe_nil t t)       t)
      ((maybe_nil t alf.nil) t)
    )
)

(declare-const or (-> (! Type :var U :implicit) U Bool (maybe_nil Bool U)) :left-assoc-nil)
(declare-const and (-> (! Type :var U :implicit) Bool U (maybe_nil Bool U)) :right-assoc-nil)
(declare-const not (-> Bool Bool))
(declare-const = (-> (! Type :var T :implicit) T T Bool))


(program substitute
  ((T Type) (U Type) (S Type) (x S) (y S) (f (-> T U)) (a T) (z U))
  (S S U) U
  (
  ((substitute x y x)     y)
  ((substitute x y (f a)) (_ (substitute x y f) (substitute x y a)))
  ((substitute x y z)     z)
  )
)


(declare-rule eq-subs
   ((f Bool) (a Bool) (b Bool))
   :premises (f (= a b))
   :args ()
   :conclusion (substitute a b f)
)
