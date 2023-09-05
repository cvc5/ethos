(include "./Builtin.smt2")

(declare-const forall (-> (! Type :var A :implicit) A Bool Bool))

(declare-const exists (-> (! Type :var A :implicit) A Bool Bool))


; maybe just change to lists

(declare-const @k.QUANTIFIERS_SKOLEMIZE (-> (! Type :var T :implicit) T Bool T))
