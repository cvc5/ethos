(include "../theories/Builtin.smt2")
(include "../theories/Arith.smt2")

(declare-sort Bag 1)

; NOTE: permits non-set types
(declare-const bag.empty (-> (! Type :var T) T))

(declare-const bag.union_max (-> (! Type :var T :implicit) (Bag T) (Bag T) (Bag T)))
(declare-const bag.union_disjoint (-> (! Type :var T :implicit) (Bag T) (Bag T) (Bag T)))
(declare-const bag.inter_min (-> (! Type :var T :implicit) (Bag T) (Bag T) (Bag T)))
(declare-const bag.difference_subtract (-> (! Type :var T :implicit) (Bag T) (Bag T) (Bag T)))
(declare-const bag.difference_remove (-> (! Type :var T :implicit) (Bag T) (Bag T) (Bag T)))
(declare-const bag.subbag (-> (! Type :var T :implicit) (Bag T) (Bag T) Bool))
(declare-const bag.count (-> (! Type :var T :implicit) T (Bag T) Int))
(declare-const bag (-> (! Type :var T :implicit) T Int (Bag T)))
(declare-const bag.member (-> (! Type :var T :implicit) T (Bag T) Bool))
(declare-const bag.card (-> (! Type :var T :implicit) (Bag T) Int))
(declare-const bag.choose (-> (! Type :var T :implicit) (Bag T) T))
(declare-const bag.duplicate_removal (-> (! Type :var T :implicit) (Bag T) (Bag T)))
(declare-const bag.is_singleton (-> (! Type :var T :implicit) (Bag T) Bool))


;(declare-const bag.from_set (# x term (apply f_bag.from_set x)))
;(declare-const bag.to_set (# x term (apply f_bag.to_set x)))
;(declare-const bag.map (-> (! Type :var T :implicit) (Bag T) (Bag T) (Bag T)))
;(declare-const bag.filter (-> (! Type :var T :implicit) (Bag T) (Bag T) (Bag T)))
;(declare-const bag.fold (# x term (# y term (# z term (apply (apply (apply f_bag.fold x) y) z)))))
;(declare-const table.product (-> (! Type :var T :implicit) (Bag T) (Bag T) (Bag T))) f_table.product x) y))))
