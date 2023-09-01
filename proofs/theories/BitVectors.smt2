; Since we don't have full support for scopes, we just import all of Ints for now
(include "../theories/Ints.smt2")

;(declare-const BitVec 
;  (-> 
;    (! Int :var w)
;    (! Type :requires ((alf.is_neg w) false))))

(declare-const BitVec (-> Int Type))
; TODO: requires
(declare-consts <binary> (BitVec (alf.len alf.self)))
(declare-consts <hexadecimal> (BitVec (alf.len alf.self)))

(declare-const concat (->
  (! Int :var n :implicit)
  (! Int :var m :implicit)
  (BitVec n)
  (BitVec m)
  (BitVec (alf.add n m))))

(declare-const extract (->
  (! Int :var n :implicit)
  (! Int :var h)
  (! Int :var l)
  (BitVec n)
  (!
    (BitVec (alf.add h (alf.add (alf.neg l) 1)))
      :requires ((alf.is_neg l) false)
      ; TODO: more conditions
  ))
)

(declare-const repeat 
    (-> Int 
        (! Int :var m :implicit) 
        (! Int :var n :implicit) 
        (BitVec m)
        (BitVec n)
    ) 
)

(declare-const bvnot
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m))
)

(declare-const bvand
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
    :left-assoc
)

(declare-const bvor
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
    :left-assoc
)

(declare-const bvnand
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m)) 
)

(declare-const bvnor
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m)) 
)

(declare-const bvxor
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m)) 
    :left-assoc
)

(declare-const bvxnor
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
)

(declare-const bvcomp
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec 1))
)

(declare-const bvneg
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m))
)

(declare-const bvadd
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m)) 
    :left-assoc
)

(declare-const bvmul
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
    :left-assoc
)

(declare-const bvudiv
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
)

(declare-const bvurem
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m)) 
)

(declare-const bvsub
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
)

(declare-const bvsdiv
  (-> (! Int :var m :implicit) 
      (BitVec m) (BitVec m) (BitVec m)) 
)

(declare-const bvsrem
  (-> (! Int :var m :implicit) 
      (BitVec m) (BitVec m) (BitVec m)) 
)

(declare-const bvsmod
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
)

(declare-const bvult
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) Bool) 
    :chainable and
)

(declare-const bvule
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) Bool) 
)

(declare-const bvugt
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) Bool) 
)

(declare-const bvuge
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) Bool) 
)

(declare-const bvslt
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) Bool)
)

(declare-const bvsle
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) Bool)
)

(declare-const bvsgt
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) Bool) 
)
  
(declare-const bvsge
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) Bool) 
)   

(declare-const bvshl
    (-> (! Int :var m :implicit) 
        (! Int :var n :implicit) 
        (BitVec m) (BitVec n) (BitVec m))
)
 
(declare-const bvlshr
    (-> (! Int :var m :implicit) 
        (! Int :var n :implicit) 
    (BitVec m) (BitVec n) (BitVec m))
)

(declare-const zero_extend
    (-> (! Int :var i) 
        (! Int :var m :implicit) 
        (! Int :var n :implicit) 
        (BitVec m) (BitVec n))
)

(declare-const sign_extend
    (-> (! Int :var i) 
        (! Int :var m :implicit) 
        (! Int :var n :implicit) 
        (BitVec m) (BitVec n))
)

(declare-const rotate_left
    (-> (! Int :var i) 
        (! Int :var m :implicit) 
        (BitVec m) (BitVec m))
)
 
(declare-const rotate_right
    (-> (! Int :var i) 
        (! Int :var m :implicit) 
        (BitVec m) (BitVec m))
)
 
(declare-const pop_count
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m))
)
   
(declare-const reduce_and
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec 1))
)

(declare-const reduce_or
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec 1))
)

(declare-const reduce_xor
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec 1))
)

(declare-const bvite
    (-> (! Int :var m :implicit) 
        (BitVec 1) (BitVec m) (BitVec m) (BitVec m))
)

(declare-const bv1ult
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec 1))
)
