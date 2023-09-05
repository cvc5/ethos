
(declare-type @Pair (Type Type))
(declare-const @pair (-> (! Type :var U :implicit) (! Type :var T :implicit) U T (@Pair U T)))

; Returns true if c is a rational between zero and one, inclusive
(program between_zero_and_one ((R Type) (c R))
  (R) Bool
  (
    ((between_zero_and_one c) 
      (alf.ite (alf.is_neg c)
        false
        (alf.ite (alf.is_eq c 1)
          true
          (alf.is_neg (alf.add c (alf.neg 1.0))))))
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

; untyped list
(declare-sort @List 0)
(declare-const @list (-> (! Type :var T :implicit) T @List @List) :right-assoc-nil)

