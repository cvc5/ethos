; Meta-inclusion for cvc5 rules and extra rules

(include "./Builtin.smt2")
(include "./Booleans.smt2")
(include "./Arrays.smt2")
(include "./Uf.smt2")
(include "./Arith.smt2")
(include "../theories/FloatingPoints.smt2")
(include "../theories/Transcendentals.smt2")
(include "../theories/BitVectors.smt2")
(include "./Strings.smt2")
(include "../theories/Sets.smt2")
(include "../theories/Bags.smt2")
(include "../theories/FiniteFields.smt2")
(include "./Quantifiers.smt2")
(include "../theories/Datatypes.smt2")
(include "../theories/SepLogic.smt2")

; TODO: proper place for these
(declare-const fmf.card (-> Type Int Bool))
(declare-sort ho-elim-sort 1)

; skolems
;INPUT_VARIABLE
;SHARED_SELECTOR
;HO_TYPE_MATCH_PRED

; evaluate, for all theories
(program run_evaluate ((T Type) (S Type) 
                       (x T) (y T) (z S) (ys S :list)
                       (b Bool) (n Int) (m Int))
    (S) S
    (
      ; core
      ((run_evaluate (= x y))           (alf.is_eq (run_evaluate x) (run_evaluate y)))
      ((run_evaluate (ite b x y))       (alf.ite (run_evaluate b) (run_evaluate x) (run_evaluate y)))
      ((run_evaluate (or x ys))         (alf.or (run_evaluate x) (run_evaluate ys)))
      ((run_evaluate (and x ys))        (alf.and (run_evaluate x) (run_evaluate ys)))
  
      ; arithmetic
      ((run_evaluate (< x z))           (alf.is_neg (run_evaluate (- x z))))
      ((run_evaluate (<= x z))          (let ((d (run_evaluate (- x z))))
                                          (alf.or (alf.is_neg d) (alf.is_zero d))))
      ((run_evaluate (> x z))           (alf.is_neg (run_evaluate (- z x))))
      ((run_evaluate (>= x z))          (let ((d (run_evaluate (- z x))))
                                          (alf.or (alf.is_neg d) (alf.is_zero d))))
      ((run_evaluate (+ x ys))          (alf.add (run_evaluate x) (run_evaluate ys)))
      ((run_evaluate (- x z))           (alf.add (run_evaluate x) (alf.neg (run_evaluate z))))
      ((run_evaluate (* x ys))          (alf.mul (run_evaluate x) (run_evaluate ys)))
      ((run_evaluate (u- x))            (alf.neg (run_evaluate x)))
      ((run_evaluate (/ x y))           (alf.qdiv (run_evaluate x) (run_evaluate y)))
      ((run_evaluate (/_total x y))     (let ((d (run_evaluate y)))
                                          (alf.ite (alf.is_eq (alf.to_q d) 0.0) 0.0 (alf.qdiv (run_evaluate x) d))))
      ((run_evaluate (div x y))         (alf.zdiv (run_evaluate x) (run_evaluate y)))
      ((run_evaluate (div_total x y))   (let ((d (run_evaluate y)))
                                          (alf.ite (alf.is_eq d 0) 0 (alf.zdiv (run_evaluate x) d))))

      ; strings
      ((run_evaluate (str.++ x y))      (alf.concat (run_evaluate x) (run_evaluate y)))
      ((run_evaluate (str.len x))       (alf.len (run_evaluate x)))
      ((run_evaluate (str.substr x n m))(alf.extract (run_evaluate n)
                                          (alf.add (run_evaluate n) (run_evaluate m))
                                          (run_evaluate x)))
      ; bitvectors
      ((run_evaluate (bvadd x ys))      (alf.add (run_evaluate x) (run_evaluate ys)))
      ((run_evaluate (bvsub x y))       (alf.add (run_evaluate x) (alf.neg (run_evaluate y))))
      ((run_evaluate (bvmul x ys))      (alf.mul (run_evaluate x) (run_evaluate ys)))
      ((run_evaluate (concat x ys))     (alf.concat (run_evaluate x) (run_evaluate ys)))
      ((run_evaluate (extract m n x))   (alf.extract n m (run_evaluate x))) ; note swap n/m
      ((run_evaluate (bvult x y))       (run_evaluate (< (alf.to_z x) (alf.to_z y))))
      ((run_evaluate (bvule x y))       (run_evaluate (<= (alf.to_z x) (alf.to_z y))))
      ((run_evaluate (bvugt x y))       (run_evaluate (> (alf.to_z x) (alf.to_z y))))
      ((run_evaluate (bvuge x y))       (run_evaluate (>= (alf.to_z x) (alf.to_z y))))
  
      ((run_evaluate z)                 z)
    )
)

(declare-rule evaluate ((U Type) (t U))
  :args (t)
  :conclusion (= t (run_evaluate t)))
