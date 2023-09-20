
(declare-const = (-> (! Type :var T) T T Bool))

(declare-const not (-> Bool Bool))


(declare-sort U 0)
(define-fun f_true ((x U)) Bool true)


(declare-rule trust ((f Bool))
   :premises ()
   :args (f)
   :conclusion f
)

(declare-const a U)

(step a1 true :rule trust :args ((f_true a)))
