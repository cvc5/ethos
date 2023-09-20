(declare-sort Int 0)
(declare-consts <numeral> Int)

(declare-type BitVec (Int)) 


(declare-const bvadd (->
  (! Int :var n :implicit)
  (BitVec n)
  (BitVec n)
  (BitVec n)))

(declare-const bvconcat (->
  (! Int :var n :implicit)
  (! Int :var m :implicit)
  (BitVec n)
  (BitVec m)
  (BitVec (alf.add n m))))
  

(declare-fun x () (BitVec 2))
(declare-fun y () (BitVec 3))
(define-fun z () (BitVec 5) (bvconcat x y))

