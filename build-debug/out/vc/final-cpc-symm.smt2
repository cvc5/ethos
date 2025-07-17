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

; The final embedding of SMT-LIB terms that are relevant to the VC.
; In other words, this defines the Herbrand universe.
(declare-datatype sm.Term
  (
  ; user-decl: $smd_sm.True
  (sm.True)
  ; user-decl: $smd_sm.False
  (sm.False)
  ; user-decl: $smd_sm.Numeral
  (sm.Numeral (sm.Numeral.arg1 Int))
  ; user-decl: $smd_sm.Rational
  (sm.Rational (sm.Rational.arg1 Real))
  ; user-decl: $smd_sm.String
  (sm.String (sm.String.arg1 String))
  ; user-decl: $smd_sm.Binary
  (sm.Binary (sm.Binary.arg1 Int) (sm.Binary.arg2 Int))
  ; user-decl: $smd_sm.Apply
  (sm.Apply (sm.Apply.arg1 sm.Term) (sm.Apply.arg2 sm.Term))
  ; user-decl: $smd_sm.Skolem
  (sm.Skolem (sm.Skolem.arg1 tsm.Type) (sm.Skolem.arg2 sm.Term) (sm.Skolem.arg3 Int))
  ; user-decl: $smd_sm.Const
  (sm.Const (sm.Const.arg1 tsm.Type) (sm.Const.arg2 Int))
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
  ; user-decl: $smd_eo.Type
  (eo.Type)
  ; user-decl: $smd_eo.Stuck
  (eo.Stuck)
  ; user-decl: $smd_eo.Apply
  (eo.Apply (eo.Apply.arg1 eo.Term) (eo.Apply.arg2 eo.Term))
  ; user-decl: $smd_eo.FunType
  (eo.FunType (eo.FunType.arg1 eo.Term) (eo.FunType.arg2 eo.Term))
  ; user-decl: $smd_eo.SmtTerm
  (eo.SmtTerm (eo.SmtTerm.arg1 sm.Term))
  ; user-decl: $smd_eo.SmtType
  (eo.SmtType (eo.SmtType.arg1 tsm.Type))
  ; user-decl: $smd_eo.SmtValue
  (eo.SmtValue (eo.SmtValue.arg1 vsm.Value))
  ; user-decl: $smd_eo.Var
  (eo.Var (eo.Var.arg1 String) (eo.Var.arg2 eo.Term))
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
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Const) (eo.SmtTerm.arg1 x1)))
    (eo.SmtType (sm.Const.arg1 (eo.SmtTerm.arg1 x1)))
  (ite true
    ($eo_typeof_main x1)
    eo.Stuck)))))))))))) :named sm.axiom.$eo_typeof))

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

; fwd-decl: $smtx_term_is_value
(declare-fun $smtx_term_is_value (sm.Term) Bool)

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

; program: $smtx_term_is_value
(assert (! (forall ((x1 sm.Term))
  (= ($smtx_term_is_value x1)
  (ite (= x1 sm.True)
    true
  (ite (= x1 sm.False)
    true
  (ite ((_ is sm.Numeral) x1)
    true
  (ite ((_ is sm.Rational) x1)
    true
  (ite ((_ is sm.String) x1)
    true
    false
))))))) :named sm.axiom.$smtx_term_is_value))

; fwd-decl: $smtx_model_eval
(declare-fun $smtx_model_eval (sm.Term) vsm.Value)

; fwd-decl: $smtx_model_lookup
(declare-fun $smtx_model_lookup (tsm.Type Int Int) vsm.Value)

; fwd-decl: $smtx_get_skolem_kind
(declare-fun $smtx_get_skolem_kind (tsm.Type sm.Term Int) Int)

; program: $smtx_model_skolem_lookup
(define-fun $smtx_model_skolem_lookup ((x1 tsm.Type) (x2 sm.Term) (x3 Int)) vsm.Value
    ($smtx_model_lookup x1 ($smtx_get_skolem_kind x1 x2 x3) x3)
)

; program: $smtx_const_predicate_internal
(define-fun $smtx_const_predicate_internal ((x1 tsm.Type) (x2 sm.Term) (x3 Int) (x4 vsm.Value)) Bool
    true
)

; program: $smtx_const_predicate
(define-fun $smtx_const_predicate ((x1 tsm.Type) (x2 sm.Term) (x3 Int)) Bool
    ($smtx_const_predicate_internal x1 x2 x3 ($smtx_model_skolem_lookup x1 x2 x3))
)

; program: $smtx_model_eval_apply
(define-fun $smtx_model_eval_apply ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Map) x1)
    ($smtx_map_lookup (vsm.Map.arg2 x1) x2)
    vsm.NotValue
))

; program: $smtx_model_eval
(assert (! (forall ((x1 sm.Term))
  (= ($smtx_model_eval x1)
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
    ($smtx_model_lookup (sm.Const.arg1 x1) 0 (sm.Const.arg2 x1))
  (ite ((_ is sm.Skolem) x1)
    ($smtx_model_skolem_lookup (sm.Skolem.arg1 x1) (sm.Skolem.arg2 x1) (sm.Skolem.arg3 x1))
    (ite ($smtx_term_is_value x1) (vsm.Term x1) vsm.NotValue)
))))))))) :named sm.axiom.$smtx_model_eval))

; program: $eo_model_sat
(assert (! (forall ((x1 eo.Term))
  (= ($eo_model_sat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite ((_ is eo.SmtTerm) x1)
    (ite (and ((_ is vsm.Term) ($smtx_model_eval (eo.SmtTerm.arg1 x1))) (= (vsm.Term.arg1 ($smtx_model_eval (eo.SmtTerm.arg1 x1))) sm.True)) (eo.SmtTerm sm.True) (eo.SmtTerm sm.False))
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

; The constant predicate holds for the model value of a constant.
(assert (! (forall ((T tsm.Type) (k sm.Term) (i Int))
  ($smtx_const_predicate T k i))
 :named sm.model_is_value))

;;; The verification condition

;;;; final verification condition for $eovc_symm
(assert (! (exists ((x1 sm.Term))
  (= ($eovc_symm (eo.SmtTerm x1)) (eo.SmtTerm sm.True))) :named sm.conjecture.$eovc_symm))


(check-sat)
