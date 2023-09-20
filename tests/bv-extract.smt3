(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-const BitVec (-> Int Type))


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
