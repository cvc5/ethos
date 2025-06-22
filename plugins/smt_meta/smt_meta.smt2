(set-logic HO_ALL)

(declare-datatype sm.Term
  (
  ; Core
  (sm.Type)
  (sm.FunType (sm.FunType.arg1 sm.Term) (sm.FunType.arg2 sm.Term))
  (sm.Apply (sm.Apply.arg1 sm.Term) (sm.Apply.arg2 sm.Term))
  (sm.Var (sm.Var.name String) (sm.Var.Type sm.Term))
  (sm.Const (sm.Const.id Int) (sm.Const.Type sm.Term))  ; user constants
  (sm.Stuck)
  ; Booleans
  (sm.BoolType)
  (sm.true)
  (sm.false)
  ; Lists
  (sm.ListType)
  (sm.List.cons)
  (sm.List.nil)
  ; builtin literal types
  (sm.Numeral (sm.Numeral.val Int))
  (sm.Rational (sm.Rational.val Real))
  (sm.Decimal (sm.Decimal.val Real))
  (sm.String (sm.String.val String))
  (sm.Binary (sm.Binary.width Int) (sm.Binary.val Int))
  (sm.Hexadecimal (sm.Hexadecimal.width Int) (sm.Hexadecimal.val Int))
  ; GENERATE user declarations
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
    (= ($eo_requires x1 x2 x3) sm.Stuck))
))

; program: $eo_hash
(declare-const $eo_hash (-> sm.Term sm.Term))
(assert (forall ((x sm.Term))
  (=> (not (= x sm.Stuck))
    ((_ is sm.Numeral) ($eo_hash x)))))
(assert (forall ((x sm.Term) (y sm.Term))
  (=> (and (not (= x sm.Stuck)) (not (= y sm.Stuck))
    (= ($eo_hash x) ($eo_hash y))) (= x y))))

; program: $eo_add
(declare-const $eo_add (-> sm.Term sm.Term sm.Term))
(assert (forall ((x1 sm.Term) (x2 sm.Term))
  (ite (and ((_ is sm.Numeral) x1) ((_ is sm.Numeral) x2))
    (= ($eo_add x1 x2) (sm.Numeral (+ (sm.Numeral.val x1) (sm.Numeral.val x1))))
    (= ($eo_add x1 x2) sm.Stuck))
))

; program: $eo_typeof_apply
(declare-const $eo_typeof_apply (-> sm.Term sm.Term sm.Term))
; TODO

; program: $eo_typeof
(declare-const $eo_typeof (-> sm.Term sm.Term))
(assert (forall ((x1 sm.Term))
  ; Core
  (ite (= x1 sm.Type)
    (= ($eo_typeof x1) sm.Type)
  (ite ((_ is sm.FunType) x1)
    ; (eo::requires (eo::typeof x1) Type (eo::requires (eo::typeof x2) Type Type))
    (= ($eo_typeof x1) ($eo_requires ($eo_typeof (sm.FunType.arg1 x1)) sm.Type ($eo_requires ($eo_typeof (sm.FunType.arg2 x1)) sm.Type sm.Type)))
  (ite ((_ is sm.Apply) x1)
    (= ($eo_typeof x1) ($eo_typeof_apply (sm.Apply.arg1 x1) (sm.Apply.arg2 x1)))
  (ite ((_ is sm.Var) x1)
    (= ($eo_typeof x1) (sm.Var.Type x1))
  (ite ((_ is sm.Const) x1)
    (= ($eo_typeof x1) (sm.Const.Type x1))
  ; Booleans
  (ite (= x1 sm.BoolType)
    (= ($eo_typeof x1) sm.Type)
  (ite (= x1 sm.true)
    (= ($eo_typeof x1) sm.BoolType)
  (ite (= x1 sm.false)
    (= ($eo_typeof x1) sm.BoolType)
  ; lists
  (ite (= x1 sm.ListType)
    (= ($eo_typeof x1) sm.Type)
  ;;; sm.List.cons has non-ground type, hence omitted
  (ite ((_ is sm.List.nil) x1)
    (= ($eo_typeof x1) sm.ListType)

  ; GENERATE literal type rules
  ; GENERATE user declarations
    true))))))))))
))

; MORE here


