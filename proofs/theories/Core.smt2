(include "../programs/Utils.smt2")

; Bool is builtin
;(declare-type Bool ())

(declare-const ite (-> (! Type :var A :implicit) Bool A A A))
(declare-const not (-> Bool Bool))

(declare-const or (-> (! Type :var U :implicit) Bool U (maybe_nil Bool U))
   :right-assoc-nil
)
(declare-const and (-> (! Type :var U :implicit) Bool U (maybe_nil Bool U))
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

(declare-const forall (-> (! Type :var A :implicit) A Bool))

(declare-const exists (-> (! Type :var A :implicit) A Bool))

(declare-const distinct (-> (! Type :var A :implicit) A A Bool) :pairwise and)
