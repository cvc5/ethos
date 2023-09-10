(include "../programs/Utils.smt2")
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

(declare-const set.comprehension (-> (! Type :var T :implicit) @List Bool T (Set T)))

(declare-const rel.tclosure (-> (! Type :var T :implicit) (Set (Tuple T T)) (Set (Tuple T T))))
(declare-const rel.transpose (-> (! Type :var T :implicit) (Set T) (Set (nary.reverse Tuple UnitTuple T))))
(declare-const rel.product (-> (! Type :var T :implicit) (! Type :var U :implicit) (Set T) (Set U) (Set (alf.append Tuple T U))))
(declare-const rel.join (-> (! Type :var T :implicit) (! Type :var U :implicit) (Set T) (Set U) (Set (nary.join Tuple UnitTuple T U))))
(declare-const rel.group (-> (! Type :var T :implicit) @List (Set T) (Set (Set T))))

(declare-const rel.iden (-> (! Type :var T :implicit) (Set (Tuple T)) (Set (Tuple T T))))  
(declare-const rel.join_image (-> (! Type :var T :implicit) (Set (Tuple T T)) Int (Set (Tuple T))))

; the diff skolem
(declare-const @k.SETS_DEQ_DIFF (-> (! Type :var T :implicit) (Set T) (Set T) T))
(declare-const @k.RELATIONS_GROUP_PART (-> (! Type :var T :implicit) (Set (Set T)) T (Set T)))
(declare-const @k.RELATIONS_GROUP_PART_ELEMENT (-> (! Type :var T :implicit) (Set (Set T)) (Set T) T))
;SETS_CHOOSE
;SETS_FOLD_CARD
;SETS_FOLD_COMBINE
;SETS_FOLD_ELEMENTS
;SETS_FOLD_UNION
;SETS_MAP_DOWN_ELEMENT
;RELATIONS_GROUP_PART
;RELATIONS_GROUP_PART_ELEMENT
