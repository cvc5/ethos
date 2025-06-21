(set-logic HO_ALL)

(declare-datatype sm.Term
  (
  (sm.Type)
  (sm.FunType (sm.FunType.arg1 sm.Term) (sm.FunType.arg2 sm.Term))
  (sm.BoolType)
  (sm.Apply (sm.Apply.arg1 sm.Term) (sm.Apply.arg2 sm.Term))
  (sm.true)
  (sm.false)
  (sm.Numeral (sm.Numeral.val Int))
  (sm.Rational (sm.Rational.val Real))
  (sm.String (sm.String.val String))
  (sm.Binary (sm.Binary.width Int) (sm.Binary.val Int))
  (sm.Var (sm.Var.name String) (sm.Var.Type Term))
  ; MORE here
  )
)

(declare-const $eo_add (-> sm.Term sm.Term sm.Term))
(assert (forall ((sm.$x sm.Term) (sm.$y sm.Term))
    (ite (and ((_ is sm.Numeral) sm.$x) ((_ is sm.Numeral) sm.$x))
      (= ($eo_add sm.$x sm.$y) (sm.Numeral (+ (sm.Numeral.val sm.$x) (sm.Numeral.val sm.$x))))
      true)
))

; MORE here


