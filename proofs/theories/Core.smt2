; Bool is builtin
;(declare-type Bool ())

(declare-const true Bool)
(declare-const false Bool)
(declare-const ite (-> (! Type :var A :implicit) Bool A A A))
(declare-const not (-> Bool Bool))
(declare-const distinct (-> (! Type :var A :implicit) A A Bool)
   ;:pairwise
)
(declare-const or (-> Bool Bool Bool)
   :right-assoc-nil
)
(declare-const and (-> Bool Bool Bool)
   :right-assoc-nil
)
(declare-const => (-> Bool Bool Bool)
   :right-assoc
)
(declare-const xor (-> Bool Bool Bool)
   :left-assoc
)

(declare-const = (-> (! Type :var A :implicit) A A Bool)
   :chainable and
)

(declare-const forall (-> (! Type :var A :implicit) (-> A Bool) Bool))
(declare-const exists (-> (! Type :var A :implicit) (-> A Bool) Bool))
; Hilbert's choice (ε)
(declare-const choose (-> (! Type :var A :implicit) (-> A Bool) A))
(declare-const compose
   (-> (! Type :var A :implicit)
    (! Type :var B :implicit)
    (! Type :var C :implicit)
    (-> B C)
    (-> A B)
    (-> A C)
   )
)
(declare-const iden (-> (! Type :var A :implicit) A A))
(declare-const apply
(-> (! Type :var A :implicit)
    (! Type :var B :implicit)
    (-> A B) A B)
    :left-assoc-nil
)
