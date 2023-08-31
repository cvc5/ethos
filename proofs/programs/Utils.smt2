
(declare-type Pair (Type Type))

(declare-const pair (-> (! Type :var U :implicit) (! Type :var T :implicit) U T (Pair U T)))

; Returns true if c is a rational between zero and one
(program between_zero_and_one ((R Type) (c R))
  (R) Bool
  (
    ((between_zero_and_one c) (alf.and (alf.not (alf.is_neg c)) (alf.is_neg (alf.add c (alf.neg 1.0)))))
  )
)

; `check_true b`
; returns true if b is true, returns false otherwise
(program check_true ((b Bool))
  (Bool) Bool
  (
    ((check_true true) true)
    ((check_true b) false)
  )
)
