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
  (sm.Decimal (sm.Decimal.val Real))
  (sm.String (sm.String.val String))
  (sm.Binary (sm.Binary.width Int) (sm.Binary.val Int))
  (sm.Hexadecimal (sm.Hexadecimal.width Int) (sm.Hexadecimal.val Int))
  (sm.Var (sm.Var.name String) (sm.Var.Type Term))
  (sm.ListType)
  (sm.List.cons (sm.List.cons.arg1 Term) (sm.List.cons.arg2 Term))
  (sm.List.nil)
  ; MORE here
  )
)

; program: $eo_ite
(declare-const $eo_ite (-> sm.Term sm.Term sm.Term sm.Term))
(assert (forall ((x1 sm.Term) (x2 sm.Term) (x3 sm.Term))
  (ite (= x1 sm.true)
    (= ($eo_ite x1 x2 x3) x2)
  (ite (= x1 sm.false)
    (= ($eo_ite x1 x2 x3) x3)
    true))
))

; program: $eo_requires
(declare-const $eo_requires (-> sm.Term sm.Term sm.Term sm.Term))
(assert (forall ((x1 sm.Term) (x2 sm.Term) (x3 sm.Term))
  (ite (= x1 x2)
    (= ($eo_requires x1 x2 x3) x3)
    true)
))

; program: $eo_add
(declare-const $eo_add (-> sm.Term sm.Term sm.Term))
(assert (forall ((x1 sm.Term) (x2 sm.Term))
  (ite (and ((_ is sm.Numeral) x1) ((_ is sm.Numeral) x1))
    (= ($eo_add x1 x2) (sm.Numeral (+ (sm.Numeral.val x1) (sm.Numeral.val x1))))
    true)
))

; MORE here


