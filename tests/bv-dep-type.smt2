(declare-sort Int 0)

(declare-type BitVec (Int)) 

(declare-const bvadd (->
  (! Int :var n)
  (BitVec n)
  (BitVec n)
  (BitVec n)))

(declare-fun m () Int)
(declare-fun dummy () Int)

(declare-fun x () (BitVec m))
(declare-fun y () (BitVec m))
(define-fun z () (BitVec m) (bvadd m x y))

; FIXME: note that (bvadd dummy x y) also type checks
; Maybe automatically make :var n -> (Quote n) then type rule (-> (Quote x) T) matches on argument, not its type.
