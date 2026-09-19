(set-logic ALL)

(declare-datatypes ((A 0) (B 0))
  (
    ((mkA (b B)))
    ((mkB (a A)) (leaf))
  ))

(declare-fun x () A)

(assert (not (= x (mkA leaf))))
(assert (not ((_ is mkB) (b x))))

(check-sat)
