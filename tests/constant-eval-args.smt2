(declare-const true Bool)
(declare-const false Bool)

(declare-sort Int 0)
(declare-consts <numeral> Int)

(program less-than ()
  (Int Int) Bool
  (
  ((less-than 0 2) true)
  ((less-than 1 2) true)
  )
)

(declare-rule dummy ()
   :premises ()
   :args (true)
   :conclusion true
)

(step a1 true :rule dummy :premises () :args ((less-than 1 2)))

