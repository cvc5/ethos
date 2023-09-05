(include "../theories/Builtin.smt2")
(include "../theories/Arith.smt2")

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

;(define set.insert (# x term (# y term (apply (apply f_set.insert x) y))))


;(define rel.join (# x term (# y term (apply (apply f_rel.join x) y))))
;(define rel.product (# x term (# y term (apply (apply f_rel.product x) y))))
;(define rel.transpose (# x term (apply f_rel.transpose x)))
;(define rel.tclosure (# x term (apply f_rel.tclosure x)))
;(define rel.iden (# x term (apply f_rel.iden x)))
;(define rel.join_image (# x term (# y term (apply (apply f_rel.join_image x) y))))


; the diff skolem
(declare-const @k.SETS_DEQ_DIFF (-> (! Type :var T :implicit) (Set T) (Set T) T))
