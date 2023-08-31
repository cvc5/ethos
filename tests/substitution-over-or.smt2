(program maybe_nil ((T Type) (t T))
    (T T) T
    (
      ((maybe_nil t t)       t)
      ((maybe_nil t alf.nil) t)
    )
)

(declare-const or (-> (! Type :var U :implicit) Bool U (maybe_nil Bool U)) :right-assoc-nil)
(declare-const and (-> (! Type :var U :implicit) Bool U (maybe_nil Bool U)) :right-assoc-nil)
(declare-const not (-> Bool Bool))
(declare-const = (-> (! Type :var T :implicit) T T Bool))

(program append 
  ((h Bool) (t Bool :list))
  (Bool Bool) Bool
  (
  ((append h t) (or h t))
  )
)

(program substitute-over-or
  ((x Bool) (y Bool) (z Bool) (l Bool :list))
  (Bool Bool Bool) Bool
  (
  ((substitute-over-or x y (or x l)) (append y (substitute-over-or x y l)))
  ((substitute-over-or x y (or z l)) (append z (substitute-over-or x y l)))
  ((substitute-over-or x y alf.nil)  alf.nil)
  )
)


(declare-rule eq-subs-over-or
   ((f Bool) (a Bool) (b Bool))
   :premises (f (= a b))
   :args ()
   :conclusion (substitute-over-or a b f)
)
