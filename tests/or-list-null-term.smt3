(program maybe_nil ((T Type) (t T))
    (T T) T
    (
      ((maybe_nil t t)       t)
      ((maybe_nil t alf.nil) t)
    )
)

(declare-const or (-> Bool Bool Bool) :left-assoc-nil)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil)

(declare-const a Bool)
(declare-const b Bool)

(declare-rule and_elim1 ((f Bool) (g Bool :list))
   :premises ((and f g))
   :args ()
   :conclusion f
)
(declare-rule or_elim1 ((f Bool :list) (g Bool))
   :premises ((or f g))
   :args ()
   :conclusion f
)

(assume a1 (or a b b b))
(assume a2 (and a b b b))

(step a3 (or a b b) :rule or_elim1 :premises (a1))
(step a4 a :rule and_elim1 :premises (a2))

