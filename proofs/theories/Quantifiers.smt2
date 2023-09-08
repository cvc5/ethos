(include "../programs/Utils.smt2")

(declare-const forall (-> @List Bool Bool))

(declare-const exists (-> @List Bool Bool))

(declare-const witness (-> (! Type :var T :implicit) T Bool T))


; maybe just change to lists

(declare-const @k.QUANTIFIERS_SKOLEMIZE (-> (! Type :var T :implicit) Bool T T))
