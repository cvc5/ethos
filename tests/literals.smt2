
(declare-sort Int 0)
(declare-consts <numeral> Int)

(declare-const and (-> Bool Bool Bool))

(program select (Int Bool) Bool
  ((f1 Bool) (f2 Bool))
  ; cases
  (
  ((select 0 (and f1 f2)) f1)
  ((select 1 (and f1 f2)) f2)
  )
)

(declare-rule and_elim ((f Bool) (g Bool) (i Int))
   :premises ((and f g))
   :args (i)
   :requires ((i 0))     ; dummy, only succeeds if i==0
   :conclusion (select i (and f g))
)


(declare-fun P () Bool)
(declare-fun Q () Bool)
(assume a0 (and P Q))
(step a1 P :rule and_elim :premises (a0) :args (0))

