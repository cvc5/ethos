(declare-const true Bool)
(declare-const false Bool)
(declare-const and (-> Bool Bool Bool) :right-assoc)

(declare-const distinct (-> (! Type :var T :implicit) T T Bool) :pairwise and)


(declare-rule identity
   ((a Bool))
   :premises ()
   :args (a)
   :conclusion a
)

(declare-sort U 0)

(declare-const a U)
(declare-const b U)
(declare-const c U)

; shows distinct is syntax sugar for pairwise construction
(step a1 (and (distinct a b) (distinct a c) (distinct b c)) :rule identity :args ((distinct a b c)))
