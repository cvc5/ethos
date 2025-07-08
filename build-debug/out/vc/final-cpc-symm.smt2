(set-logic UFDTSNIRA)
; This is both a valid *.smt2 and *.eo file after filling in the templates.
; For consistency we name it *.eo.

; The final embedding of SMT-LIB types that are relevant to the VC.
(declare-datatype tsm.Type
  (
  ; the Boolean type
  (tsm.Bool)
  ; uninterpreted sorts
  (tsm.USort (tsm.USort.arg1 Int))
  ; The application of SMT-LIB types
  (tsm.Apply (tsm.Apply.arg1 tsm.Type) (tsm.Apply.arg2 tsm.Type))
  ; user-decl: Int
  (tsm.Int)
  ; user-decl: Real
  (tsm.Real)
  ; user-decl: Char
  (tsm.Char)
  ; user-decl: Seq
  (tsm.Seq)
  ; user-decl: BitVec
  (tsm.BitVec)

  ; error sort
  (tsm.NullSort (tsm.NullSort.arg1 Int))
  )
)

; carrying the literal types?


; The final embedding of SMT-LIB terms that are relevant to the VC.
; In other words, this defines the Herbrand universe.
(declare-datatype sm.Term
  (
  ; The application of SMT-LIB terms
  (sm.Apply (sm.Apply.arg1 sm.Term) (sm.Apply.arg2 sm.Term))
  ; Booleans
  ; NOTE: these are inlined for efficiency and to ensure there are no Boolean subterms
  (sm.True)
  (sm.False)
  ; builtin literals
  (sm.Numeral (sm.Numeral.arg1 Int))
  (sm.Rational (sm.Rational.arg1 Real))
  (sm.String (sm.String.arg1 String))
  (sm.Binary (sm.Binary.arg1 Int) (sm.Binary.arg2 Int))
  ; free constants
  (sm.Const (sm.Const.arg1 tsm.Type) (sm.Const.arg2 Int))
  ; skolems
  (sm.Skolem (sm.Skolem.arg1 tsm.Type) (sm.Skolem.arg2 sm.Term) (sm.Skolem.arg3 Int))
  ; user-decl: not
  (sm.not)
  ; user-decl: and
  (sm.and)
  ; user-decl: ite
  (sm.ite)
  ; user-decl: =
  (sm.=)

  )
)

; The final embedding of Eunoia terms that are relevant to the VC.
; SMT-LIB terms, types and values are embedded in this datatype.
; We require a mutually recursive datatype, since these are
; inter-dependent.
(declare-datatypes ((eo.Term 0) (vsm.Value 0) (msm.Map 0))
  (
  (
  ; The type of types in Eunoia
  (eo.Type)
  ; The Eunoia function type.
  (eo.FunType (eo.FunType.arg1 eo.Term) (eo.FunType.arg2 eo.Term))
  ; Application of a Eunoia term
  (eo.Apply (eo.Apply.arg1 eo.Term) (eo.Apply.arg2 eo.Term))
  ; The Eunoia representation of an SMT-LIB term
  (eo.SmtTerm (eo.SmtTerm.arg1 sm.Term))
  ; The Eunoia representation of an SMT-LIB type
  (eo.SmtType (eo.SmtType.arg1 tsm.Type))
  ; The Eunoia representation of an SMT-LIB value
  ;(eo.SmtValue (eo.SmtValue.arg1 vsm.Value))
  (eo.Var (eo.Var.arg1 String) (eo.Var.arg2 eo.Term))
  ; "stuckness"
  (eo.Stuck)
  ; user-decl: $eo_List
  (eo.$eo_List)

  )
  (
  ; map with an index type
  ; valueness: $smtx_map_is_value
  (vsm.Map (vsm.Map.arg1 tsm.Type) (vsm.Map.arg2 msm.Map))
  ; uninterpreted constants
  ; valueness: $smtx_usort_is_value
  (vsm.UValue (vsm.UValue.arg1 tsm.Type) (vsm.UValue.arg2 Int))
  ; an SMT value represented by an SMT-LIB term, e.g. Int/Real/String.
  ; valueness: $smtx_is_value
  (vsm.Term (vsm.Term.arg1 sm.Term))
  ; A non-value
  (vsm.NotValue)
  )
  (
  ; (msm.Map.cons i e M) maps i -> e, as well as mappings in M
  (msm.Map.cons (msm.Map.cons.arg1 vsm.Value) (msm.Map.cons.arg2 vsm.Value) (msm.Map.cons.arg3 msm.Map))
  ; (msm.Map.default e) maps all remaining elements in the sort to e
  (msm.Map.default (msm.Map.default.arg1 vsm.Value))
  ))
)

;;; User defined symbols

; fwd-decl: $eo_typeof
(declare-fun $eo_typeof (eo.Term) eo.Term)

; program: $eo_apply
(define-fun $eo_apply ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite true
    (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck)) eo.Stuck (eo.Apply x1 x2))
    eo.Stuck)))

; program: $eo_fun_type
(define-fun $eo_fun_type ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite true
    (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck)) eo.Stuck (eo.FunType x1 x2))
    eo.Stuck)))

; program: $eo_requires
(define-fun $eo_requires ((x1 eo.Term) (x2 eo.Term) (x3 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck) (= x3 eo.Stuck))
    eo.Stuck
  (ite true
    (ite (and (not (= x1 eo.Stuck)) (= x1 x2)) x3 eo.Stuck)
    eo.Stuck)))

; fwd-decl: $eo_hash
(declare-fun $eo_hash (eo.Term) eo.Term)

; fwd-decl: $eo_typeof_main
(declare-fun $eo_typeof_main (eo.Term) eo.Term)

; program: $eo_typeof
(assert (! (forall ((x1 eo.Term))
  (= ($eo_typeof x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.True))
    (eo.SmtType tsm.Bool)
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.False))
    (eo.SmtType tsm.Bool)
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Numeral) (eo.SmtTerm.arg1 x1)))
    (eo.SmtType tsm.Int)
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Rational) (eo.SmtTerm.arg1 x1)))
    (eo.SmtType tsm.Real)
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.String) (eo.SmtTerm.arg1 x1)))
    (eo.SmtType (tsm.Apply tsm.Seq tsm.Char))
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Binary) (eo.SmtTerm.arg1 x1)))
    eo.Type
  (ite ((_ is eo.Var) x1)
    (eo.Var.arg2 x1)
  (ite true
    ($eo_typeof_main x1)
    eo.Stuck))))))))))) :named sm.axiom.$eo_typeof))

; program: $mk_symm
(define-fun $mk_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Apply) (eo.SmtTerm.arg1 x1)) ((_ is sm.Apply) (sm.Apply.arg1 (eo.SmtTerm.arg1 x1))) (= (sm.Apply.arg1 (sm.Apply.arg1 (eo.SmtTerm.arg1 x1))) sm.=))
    (eo.SmtTerm (sm.Apply (sm.Apply sm.= (sm.Apply.arg2 (eo.SmtTerm.arg1 x1))) (sm.Apply.arg2 (sm.Apply.arg1 (eo.SmtTerm.arg1 x1)))))
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Apply) (eo.SmtTerm.arg1 x1)) ((_ is sm.Apply) (sm.Apply.arg2 (eo.SmtTerm.arg1 x1))) ((_ is sm.Apply) (sm.Apply.arg1 (sm.Apply.arg2 (eo.SmtTerm.arg1 x1)))) (= (sm.Apply.arg1 (sm.Apply.arg1 (sm.Apply.arg2 (eo.SmtTerm.arg1 x1)))) sm.=) (= (sm.Apply.arg1 (eo.SmtTerm.arg1 x1)) sm.not))
    (eo.SmtTerm (sm.Apply sm.not (sm.Apply (sm.Apply sm.= (sm.Apply.arg2 (sm.Apply.arg2 (eo.SmtTerm.arg1 x1)))) (sm.Apply.arg2 (sm.Apply.arg1 (sm.Apply.arg2 (eo.SmtTerm.arg1 x1)))))))
    eo.Stuck))))

; program: $eo_typeof_apply
(define-fun $eo_typeof_apply ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite (and ((_ is eo.FunType) x1) (= x2 (eo.FunType.arg1 x1)))
    (eo.FunType.arg2 x1)
    eo.Stuck)))

; program: $eo_typeof_ite
(define-fun $eo_typeof_ite ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite (= x1 (eo.SmtType tsm.Bool))
    ($eo_fun_type x2 x2)
    eo.Stuck)))

; program: $eo_typeof_=
(define-fun $eo_typeof_= ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_fun_type x1 (eo.SmtType tsm.Bool))
    eo.Stuck)))

; program: $eo_typeof_fun_type
(define-fun $eo_typeof_fun_type ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite (and (= x1 eo.Type) (= x2 eo.Type))
    eo.Type
    eo.Stuck)))

; program: $eo_typeof_main
(assert (! (forall ((x1 eo.Term))
  (= ($eo_typeof_main x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite (= x1 eo.Type)
    eo.Type
  (ite ((_ is eo.FunType) x1)
    ($eo_typeof_fun_type ($eo_typeof (eo.FunType.arg1 x1)) ($eo_typeof (eo.FunType.arg2 x1)))
  (ite (= x1 (eo.SmtType tsm.Bool))
    eo.Type
  (ite (= x1 (eo.SmtTerm sm.True))
    (eo.SmtType tsm.Bool)
  (ite (= x1 (eo.SmtTerm sm.False))
    (eo.SmtType tsm.Bool)
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.Int))
    eo.Type
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.Real))
    eo.Type
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.Char))
    eo.Type
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.Seq))
    ($eo_fun_type eo.Type eo.Type)
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Apply) (eo.SmtTerm.arg1 x1)) ((_ is sm.Apply) (sm.Apply.arg1 (eo.SmtTerm.arg1 x1))) (= (sm.Apply.arg1 (sm.Apply.arg1 (eo.SmtTerm.arg1 x1))) sm.ite))
    ($eo_typeof_ite ($eo_typeof (eo.SmtTerm (sm.Apply.arg2 (sm.Apply.arg1 (eo.SmtTerm.arg1 x1))))) ($eo_typeof (eo.SmtTerm (sm.Apply.arg2 (eo.SmtTerm.arg1 x1)))))
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.not))
    ($eo_fun_type (eo.SmtType tsm.Bool) (eo.SmtType tsm.Bool))
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.and))
    ($eo_fun_type (eo.SmtType tsm.Bool) ($eo_fun_type (eo.SmtType tsm.Bool) (eo.SmtType tsm.Bool)))
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Apply) (eo.SmtTerm.arg1 x1)) (= (sm.Apply.arg1 (eo.SmtTerm.arg1 x1)) sm.=))
    ($eo_typeof_= ($eo_typeof (eo.SmtTerm (sm.Apply.arg2 (eo.SmtTerm.arg1 x1)))))
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.BitVec))
    ($eo_fun_type (eo.SmtType tsm.Int) eo.Type)
  (ite ((_ is eo.Apply) x1)
    ($eo_typeof_apply ($eo_typeof (eo.Apply.arg1 x1)) ($eo_typeof (eo.Apply.arg2 x1)))
    eo.Stuck)))))))))))))))))) :named sm.axiom.$eo_typeof_main))

; fwd-decl: $eo_model_sat
(declare-fun $eo_model_sat (eo.Term) eo.Term)

; program: $smtx_map_lookup
(declare-fun $smtx_map_lookup (msm.Map vsm.Value) vsm.Value)
(assert (! (forall ((x1 msm.Map) (x2 vsm.Value))
  (= ($smtx_map_lookup x1 x2)
  (ite (and ((_ is msm.Map.cons) x1) (= x2 (msm.Map.cons.arg1 x1)))
    (msm.Map.cons.arg2 x1)
  (ite ((_ is msm.Map.cons) x1)
    ($smtx_map_lookup (msm.Map.cons.arg3 x1) x2)
    (msm.Map.default.arg1 x1)
)))) :named sm.axiom.$smtx_map_lookup))

; fwd-decl: $smtx_model_eval
(declare-fun $smtx_model_eval (sm.Term) vsm.Value)

; fwd-decl: $smtx_model_lookup
(declare-fun $smtx_model_lookup (Int Int tsm.Type) vsm.Value)

; program: $smtx_const_predicate
(define-fun $smtx_const_predicate ((x1 Int) (x2 Int) (x3 tsm.Type) (x4 vsm.Value)) Bool
  (ite (= x1 0)
    true
    false
))

; program: $smtx_model_eval_apply
(define-fun $smtx_model_eval_apply ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Map) x1)
    ($smtx_map_lookup (vsm.Map.arg2 x1) x2)
    vsm.NotValue
))

; program: $smtx_model_eval
(assert (! (forall ((x1 sm.Term))
  (= ($smtx_model_eval x1)
  (ite (= x1 sm.True)
    (vsm.Term sm.True)
  (ite (= x1 sm.False)
    (vsm.Term sm.False)
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) ((_ is sm.Apply) (sm.Apply.arg1 (sm.Apply.arg1 x1))) (= (sm.Apply.arg1 (sm.Apply.arg1 (sm.Apply.arg1 x1))) sm.ite))
    (ite (not ((_ is vsm.NotValue) ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 (sm.Apply.arg1 x1)))))) (ite (and ((_ is vsm.Term) ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 (sm.Apply.arg1 x1))))) (= (vsm.Term.arg1 ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 (sm.Apply.arg1 x1))))) sm.True)) ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_model_eval (sm.Apply.arg2 x1))) vsm.NotValue)
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) (= (sm.Apply.arg1 (sm.Apply.arg1 x1)) sm.=))
    (ite (and (not ((_ is vsm.NotValue) ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))))) (not ((_ is vsm.NotValue) ($smtx_model_eval (sm.Apply.arg2 x1))))) (vsm.Term (ite (= ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_model_eval (sm.Apply.arg2 x1))) sm.True sm.False)) vsm.NotValue)
  (ite (and ((_ is sm.Apply) x1) (= (sm.Apply.arg1 x1) sm.not))
    (ite (not ((_ is vsm.NotValue) ($smtx_model_eval (sm.Apply.arg2 x1)))) (vsm.Term (ite (not (= sm.True (vsm.Term.arg1 ($smtx_model_eval (sm.Apply.arg2 x1))))) sm.True sm.False)) vsm.NotValue)
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) (= (sm.Apply.arg1 (sm.Apply.arg1 x1)) sm.and))
    (ite (not ((_ is vsm.NotValue) ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))))) (ite (not ((_ is vsm.NotValue) ($smtx_model_eval (sm.Apply.arg2 x1)))) (vsm.Term (ite (and (= sm.True (vsm.Term.arg1 ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))))) (= sm.True (vsm.Term.arg1 ($smtx_model_eval (sm.Apply.arg2 x1))))) sm.True sm.False)) vsm.NotValue) vsm.NotValue)
  (ite ((_ is sm.Apply) x1)
    ($smtx_model_eval_apply ($smtx_model_eval (sm.Apply.arg1 x1)) ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite ((_ is sm.Const) x1)
    ($smtx_model_lookup 0 (sm.Const.arg2 x1) (sm.Const.arg1 x1))
    vsm.NotValue
)))))))))) :named sm.axiom.$smtx_model_eval))

; program: $smtx_model_sat
(define-fun $smtx_model_sat ((x1 vsm.Value)) eo.Term
  (ite (and ((_ is vsm.Term) x1) (= (vsm.Term.arg1 x1) sm.True))
    (eo.SmtTerm sm.True)
    (eo.SmtTerm sm.False)
))

; program: $eo_model_sat
(assert (! (forall ((x1 eo.Term))
  (= ($eo_model_sat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite ((_ is eo.SmtTerm) x1)
    ($smtx_model_sat ($smtx_model_eval (eo.SmtTerm.arg1 x1)))
    eo.Stuck)))) :named sm.axiom.$eo_model_sat))

; program: $eorx_symm
(define-fun $eorx_symm ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite (= x2 (eo.SmtType tsm.Bool))
    ($mk_symm x1)
    eo.Stuck)))

; program: $eor_symm
(define-fun $eor_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eorx_symm x1 ($eo_typeof x1))
    eo.Stuck)))

; program: $eovc_symm
(define-fun $eovc_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_requires ($eo_model_sat x1) (eo.SmtTerm sm.True) ($eo_requires ($eo_model_sat ($eor_symm x1)) (eo.SmtTerm sm.False) (eo.SmtTerm sm.True)))
    eo.Stuck)))



;;; Meta-level properties of models

; axiom: $eo_hash
; note: This is defined axiomatically.
(assert (! (forall ((x eo.Term))
  (=> (not (= x eo.Stuck))
    (and
      ((_ is eo.SmtTerm) ($eo_hash x))
      ((_ is sm.Numeral) (eo.SmtTerm.arg1 ($eo_hash x)))))) :named sm.hash_numeral))
(assert (! (forall ((x eo.Term) (y eo.Term))
  (=> (and (not (= x eo.Stuck)) (not (= y eo.Stuck))
    (= ($eo_hash x) ($eo_hash y))) (= x y))) :named sm.hash_injective))

; Handles free constants, skolems, and TODO: partial functions.
; If the constant predicate for a constant is satisfied,
; then we may assume that the model value for that constant is a value.
(assert (! (forall ((k Int) (i Int) (T tsm.Type))
  (=> ($smtx_const_predicate k i T ($smtx_model_lookup k i T))
      (not ((_ is vsm.NotValue) ($smtx_model_lookup k i T)))))
 :named sm.model_is_value))

;;; The verification condition

;;;; final verification condition for $eovc_symm
(assert (! (exists ((x1 sm.Term))
  (= ($eovc_symm (eo.SmtTerm x1)) (eo.SmtTerm sm.True))) :named sm.conjecture.$eovc_symm))


(check-sat)
