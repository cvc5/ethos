
(declare-type Pair (Type Type))

(declare-const pair (-> (! Type :var U :implicit) (! Type :var T :implicit) U T (Pair U T)))

; Returns true if c is a rational between zero and one
(program between_zero_and_one ((R Type) (c R))
  (R) Bool
  (
    ((between_zero_and_one c) (alf.and (alf.not (alf.is_neg c)) (alf.is_neg (alf.add c (alf.neg 1.0)))))
  )
)
