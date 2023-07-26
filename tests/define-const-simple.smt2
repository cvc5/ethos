
(declare-const true Bool)
(declare-const false Bool)
(declare-const not (-> Bool Bool))

(define-const f_true Bool true)


(declare-rule trust ((f Bool))
   :premises ()
   :args (f)
   :conclusion f
)

(step a1 true :rule trust :args (f_true))
