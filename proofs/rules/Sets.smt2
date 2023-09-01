(include "../theories/Core.smt2")
(include "../theories/Arith.smt2")
(include "../theories/Core.smt2")

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


;(declare f_set.insert term)
;(define set.insert (# x term (# y term (apply (apply f_set.insert x) y))))
;(declare f_set.filter term)
;(define set.filter (# x term (# y term (apply (apply f_set.filter x) y))))
;(declare f_set.map term)
;(define set.map (# x term (# y term (apply (apply f_set.map x) y))))
;(declare f_set.fold term)
;(define set.fold (# x term (# y term (# z term (apply (apply (apply f_set.fold x) y) z)))))


;(declare f_rel.join term)
;(define rel.join (# x term (# y term (apply (apply f_rel.join x) y))))
;(declare f_rel.product term)
;(define rel.product (# x term (# y term (apply (apply f_rel.product x) y))))
;(declare f_rel.transpose term)
;(define rel.transpose (# x term (apply f_rel.transpose x)))
;(declare f_rel.tclosure term)
;(define rel.tclosure (# x term (apply f_rel.tclosure x)))
;(declare f_rel.iden term)
;(define rel.iden (# x term (apply f_rel.iden x)))
;(declare f_rel.join_image term)
;(define rel.join_image (# x term (# y term (apply (apply f_rel.join_image x) y))))

