(declare-sort Int 0)

(declare-type BitVec (Int)) 

(declare-const bvadd (->
  (! Int :var n)
  (BitVec n)
  (BitVec n)
  (BitVec n)))
