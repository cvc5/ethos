(include "../theories/Builtin.smt2")
(include "../theories/Arith.smt2")
(include "../theories/Datatypes.smt2")

(declare-sort Set 1)

; NOTE: permits non-set types
(declare-const set.empty (-> (! Type :var T) T))
(declare-const set.universe (-> (! Type :var T) T))

(declare-const set.singleton (-> (! Type :var T :implicit) T (Set T)))
(declare-const set.union (-> (! Type :var T :implicit) (Set T) (Set T) (Set T)))
(declare-const set.inter (-> (! Type :var T :implicit) (Set T) (Set T) (Set T)))
(declare-const set.minus (-> (! Type :var T :implicit) (Set T) (Set T) (Set T)))
(declare-const set.complement (-> (! Type :var T :implicit) (Set T) (Set T)))
(declare-const set.member (-> (! Type :var T :implicit) T (Set T) Bool))
(declare-const set.subset (-> (! Type :var T :implicit) (Set T) (Set T) Bool))
(declare-const set.card (-> (! Type :var T :implicit) (Set T) Int))
(declare-const set.choose (-> (! Type :var T :implicit) (Set T) T))
(declare-const set.is_singleton (-> (! Type :var T :implicit) (Set T) Bool))

(declare-const set.filter (-> (! Type :var T :implicit) (-> T Bool) (Set T) (Set T)))
(declare-const set.map (-> (! Type :var T :implicit) (! Type :var U :implicit) (-> T U) (Set T) (Set U)))
(declare-const set.fold (-> (! Type :var T :implicit) (! Type :var U :implicit) (-> T U U) U (Set T) U))

(declare-const rel.tclosure (-> (! Type :var T :implicit) (Set (Tuple T T)) (Set (Tuple T T))))
(declare-const rel.transpose (-> (! Type :var T :implicit) (Set T) (Set (nary.reverse Tuple UnitTuple T))))
(declare-const rel.product (-> (! Type :var T :implicit) (! Type :var U :implicit) (Set T) (Set U) (Set (alf.append Tuple U T))))
(declare-const rel.join (-> (! Type :var T :implicit) (! Type :var U :implicit) (Set T) (Set U) (Set (nary.join Tuple UnitTuple U T))))

; note UnitTuple provided
(declare-const rel.iden (-> (! Type :var T :implicit) (Set (Tuple T UnitTuple)) (Set (Tuple T T))))  
(declare-const rel.join_image (-> (! Type :var T :implicit) (Set (Tuple T T)) Int (Set (Tuple T UnitTuple))))


; the diff skolem
(declare-const @k.SETS_DEQ_DIFF (-> (! Type :var T :implicit) (Set T) (Set T) T))
