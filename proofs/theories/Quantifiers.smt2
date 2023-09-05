(include "./Builtin.smt2")

(declare-const forall (-> @List Bool Bool))

(declare-const exists (-> @List Bool Bool))


; maybe just change to lists

(declare-const @k.QUANTIFIERS_SKOLEMIZE (-> (! Type :var T :implicit) Bool T T))
