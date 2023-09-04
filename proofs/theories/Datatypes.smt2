

(declare-const UnitTuple Type)
(declare-const Tuple (-> Type Type Type) :right-assoc UnitTuple)

(declare-const unit.tuple UnitTuple)
(declare-const tuple (-> (! Type :var T :implicit)
                         (! Type :var U :implicit)
                         T (! U :list) (Tuple T U)) :right-assoc unit.tuple)
