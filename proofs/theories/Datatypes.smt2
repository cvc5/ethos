

(declare-const UnitTuple Type)
(declare-const Tuple (-> Type Type Type) :right-assoc-nil UnitTuple)

(declare-const unit.tuple UnitTuple)
(declare-const tuple (-> (! Type :var T :implicit)
                         (! Type :var U :implicit)
                         T U (alf.cons Tuple T U)) :right-assoc-nil unit.tuple)
