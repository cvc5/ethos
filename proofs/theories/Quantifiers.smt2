(include "./Builtin.smt2")

(declare-const forall (-> (! Type :var A :implicit) A Bool Bool))

(declare-const exists (-> (! Type :var A :implicit) A Bool Bool))



(declare-const @k.QUANTIFIERS_SKOLEMIZE (-> (! Type :var T) Bool T))
