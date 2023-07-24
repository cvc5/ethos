; Since we don't have full support for scopes, we just import all of Ints for now
(include "../theories/Ints.smt2")

(declare-type BitVec (Int)) 

;(declare-const to_int (-> (! Int :var m :implicit) (BitVec m) Int))
(declare-const to_bv (-> (! Int :var m) Int (BitVec m)))
;(declare-const to_bv (-> Bool (BitVec 1)))

(declare-const bvempty (BitVec 0))

(declare-const <binary>
    (-> (! Int :var m :implicit)
        (BitVec m)))

(declare-const <hexadecimal>
    (-> (! Int :var m :implicit) 
        (BitVec m)))

(declare-const concat 
    (-> (! Int :var i :implicit) 
        (! Int :var j :implicit) 
        (! Int :var k :implicit) 
        (BitVec i) (BitVec j)
        (BitVec k))
)

(declare-const extract
    (-> (! Int :var m :implicit) 
        (! Int :var i) 
        (! Int :var j)
        (! Int :var k :implicit)
        (BitVec m) (BitVec k))
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
)

(declare-const bvor
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
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
)

(declare-const bvmul
    (-> (! Int :var m :implicit) 
        (BitVec m) (BitVec m) (BitVec m))
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