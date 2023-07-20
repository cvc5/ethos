(declare-sort Int 0)

(declare-type BitVec (Int)) 

(declare-const bvadd (->
  (! Int :var n)
  (BitVec n)
  (BitVec n)
  (BitVec n)))

(declare-fun m () Int)

(declare-fun x () (BitVec m))
(declare-fun y () (BitVec m))
(define-fun z () (BitVec m) (bvadd m x y))
