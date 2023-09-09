(include "../theories/Builtin.smt2")
(include "../theories/Arith.smt2")
(include "../theories/BitVectors.smt2")

(declare-const FloatingPoint
  ;(-> (! Int :var e) (! Int :var s) Type)
  (-> Int Int Type)
)
(declare-sort RoundingMode 0)

; A floating point constant is a term having 3 bitvector children.
; Note this is used for both FLOATINGPOINT_FP and CONST_FLOATINGPOINT
;(declare-const fp term)
;(define fp (# x term (# y term (# z term (apply (apply (apply fp x) y) z)))))

(declare-const fp
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (BitVec 1) (BitVec e) (BitVec s) (FloatingPoint e (alf.add s 1))))

(declare-const fp.add
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      RoundingMode (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.sub
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      RoundingMode (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.mul
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      RoundingMode (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.div
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      RoundingMode (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.fma
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      RoundingMode (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.sqrt
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.rem
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.roundToIntegral
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      RoundingMode (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.min
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.max
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.abs
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s)))
(declare-const fp.neg
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s)))

(declare-const fp.leq
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) Bool))
(declare-const fp.lt
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) Bool))
(declare-const fp.geq
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) Bool))
(declare-const fp.gt
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) Bool))
(declare-const fp.eq
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) (FloatingPoint e s) Bool))

(declare-const fp.isNormal
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) Bool))
(declare-const fp.isSubnormal
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) Bool))
(declare-const fp.isZero
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) Bool))
(declare-const fp.isInfinite
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) Bool))
(declare-const fp.isNaN
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) Bool))
(declare-const fp.isPositive
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) Bool))
(declare-const fp.isNegative
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      (FloatingPoint e s) Bool))

; rounding modes
(declare-const roundNearestTiesToEven RoundingMode)
(declare-const roundNearestTiesToAway RoundingMode)
(declare-const roundTowardPositive RoundingMode)
(declare-const roundTowardNegative RoundingMode)
(declare-const roundTowardZero RoundingMode)

(declare-const fp.to_ubv
  (->
  (! Int :var e :implicit) (! Int :var s :implicit)
  (! Int :var m :implicit) RoundingMode (FloatingPoint e s) (BitVec m)))

(declare-const fp.to_sbv
  (->
  (! Int :var e :implicit) (! Int :var s :implicit)
  (! Int :var m :implicit) RoundingMode (FloatingPoint e s) (BitVec m)))

(declare-const fp.to_real
  (-> (! Int :var e :implicit) (! Int :var s :implicit)
      RoundingMode (FloatingPoint e s) Real))

(declare-const to_fp
  (-> (! Type :var T :implicit)
      (! Int :var e) (! Int :var s) RoundingMode T (FloatingPoint e s)))
      
(declare-const to_fp_unsigned
  (-> (! Type :var T :implicit)
      (! Int :var e) (! Int :var s) RoundingMode T (FloatingPoint e s)))

; internally generated terms
(declare-const EXPONENT (-> (! Type :var T) T))
(declare-const SIGN (-> (! Type :var T) T))
(declare-const SIGNIFICAND (-> (! Type :var T) T))
(declare-const ZERO (-> (! Type :var T) T))
(declare-const INF (-> (! Type :var T) T))
(declare-const NAN (-> (! Type :var T) T))
