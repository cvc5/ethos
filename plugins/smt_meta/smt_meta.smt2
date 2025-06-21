(set-logic HO_ALL)

(declare-datatype Term
  (
  (sm.Type)
  (sm.Apply (sm.Apply.head Term) (sm.Apply.arg Term))
  (sm.True)
  (sm.False)
  (sm.Numeral (sm.Numeral.val Int))
  (sm.Rational (sm.Rational.val Real))
  (sm.String (sm.String.val String))
  (sm.Binary (sm.Binary.val Int) (sm.Binary.width Int))
  ; MORE here
  )
)

(declare-const $eo_add (-> Term Term Term))
(assert (forall ((sm.$x Term) (sm.$y Term))
    (ite (and ((_ is sm.Numeral) sm.$x) ((_ is sm.Numeral) sm.$x))
      (= ($eo_add sm.$x sm.$y) (sm.Numeral (+ (sm.Numeral.val sm.$x) (sm.Numeral.val sm.$x))))
      true)
))

; MORE here


