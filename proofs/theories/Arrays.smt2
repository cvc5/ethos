(include "../theories/Builtin.smt2")

(declare-sort Array 2)

(declare-const select (-> (! Type :var U :implicit) (! Type :var T :implicit)
                          (Array U T) U T))
(declare-const store (-> (! Type :var U :implicit) (! Type :var T :implicit)
                          (Array U T) U T (Array U T)))


; NOTE: doesn't check that T is (Array x U) for some x
(declare-const store_all (-> (! Type :var T) (! Type :var U :implicit) U T))

(declare-const eqrange (-> (! Type :var U :implicit) (! Type :var T :implicit) (! Type :var I :implicit)
                           (Array U T) (Array U T) I I Bool))

; the diff skolem
(declare-const @k.ARRAY_DEQ_DIFF
   (-> (! Type :var T :implicit) (! Type :var U :implicit) (Array T U) (Array T U) T))
