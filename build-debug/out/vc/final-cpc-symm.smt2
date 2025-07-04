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
  (tsm.NullSort)
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
(declare-datatypes ((eo.Term 0) (vsm.Value 0) (@Map 0))
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
  (eo.$eo_Var (eo.$eo_Var.arg1 String) (eo.$eo_Var.arg2 eo.Term))
  ; "stuckness"
  (eo.Stuck)
  ; user-decl: $eo_List
  (eo.$eo_List)

  )
  (
  ; map with an index type
  ; valueness: $smtx_map_is_value
  (vsm.Map (vsm.Map.arg1 @Map) (vsm.Map.arg2 tsm.Type))
  ; uninterpreted constants
  ; valueness: $smtx_usort_is_value
  (vsm.UValue (vsm.UValue.arg1 tsm.Type) (i Int))
  ; an SMT value represented by an SMT-LIB term, e.g. Int/Real/String.
  ; valueness: $smtx_is_value
  (vsm.Term (vsm.Term.arg1 sm.Term))
  ; A non-value
  (vsm.NotValue)
  )
  (
  ; (@Map.cons i e M) maps i -> e, as well as mappings in M
  (@Map.cons (@Map.cons.arg1 vsm.Value) (@Map.cons.arg2 vsm.Value) (@Map.cons.arg3 @Map))
  ; (@Map.default e) maps all remaining elements in the sort to e
  (@Map.default (@Map.default.arg1 vsm.Value))
  ))
)

;;; Utilities

; Stuckness propagates through non-nullary constructors
(define-fun $eo_FunType ((x eo.Term) (y eo.Term)) eo.Term
  (ite (or (= x eo.Stuck) (= y eo.Stuck))
    eo.Stuck
    (eo.FunType x y)))

(define-fun $eo_Apply ((x eo.Term) (y eo.Term)) eo.Term
  (ite (or (= x eo.Stuck) (= y eo.Stuck))
    eo.Stuck
    (eo.Apply x y)))

;;; Core operators

; Note that these cannot be lifted further since their semantics wrt
; stuckness is non-standard.
; TODO: maybe better if these are lifted and made a special case?

; axiom: $eo_is_ok
(define-fun $eo_is_ok ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    (eo.SmtTerm sm.False)
    (eo.SmtTerm sm.True)))

; axiom: $eo_ite
(define-fun $eo_ite ((x1 eo.Term) (x2 eo.Term) (x3 eo.Term)) eo.Term
  (ite (= x1 (eo.SmtTerm sm.True))
    x2
  (ite (= x1 (eo.SmtTerm sm.False))
    x3
    eo.Stuck)))

; axiom: $eo_requires
(define-fun $eo_requires ((x1 eo.Term) (x2 eo.Term) (x3 eo.Term)) eo.Term
  (ite (and (not (= x1 eo.Stuck)) (not (= x2 eo.Stuck)) (= x1 x2))
    x3
    eo.Stuck))

;;; User defined symbols

; fwd-decl: $eo_typeof
(declare-fun $eo_typeof (eo.Term) eo.Term)

; program: $eo_smt_term
(define-fun $eo_smt_term ((x1 sm.Term)) eo.Term
  (ite false
    eo.Stuck
  (ite true
    (eo.SmtTerm x1)
    eo.Stuck)))

; program: $eo_smt_type
(define-fun $eo_smt_type ((x1 tsm.Type)) eo.Term
  (ite false
    eo.Stuck
  (ite true
    (eo.SmtType x1)
    eo.Stuck)))

; program: $eo_mk_numeral
(define-fun $eo_mk_numeral ((x1 Int)) eo.Term
  (ite false
    eo.Stuck
  (ite true
    (eo.SmtTerm (sm.Numeral x1))
    eo.Stuck)))

; program: $eo_mk_rational
(define-fun $eo_mk_rational ((x1 Real)) eo.Term
  (ite false
    eo.Stuck
  (ite true
    (eo.SmtTerm (sm.Rational x1))
    eo.Stuck)))

; program: $eo_mk_string
(define-fun $eo_mk_string ((x1 String)) eo.Term
  (ite false
    eo.Stuck
  (ite true
    (eo.SmtTerm (sm.String x1))
    eo.Stuck)))

; program: $eo_binary
(define-fun $eo_binary ((x1 Int) (x2 Int)) eo.Term
  (ite false
    eo.Stuck
  (ite true
    (eo.SmtTerm (sm.Binary x1 x2))
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
  (ite ((_ is eo.$eo_Var) x1)
    (eo.$eo_Var.arg2 x1)
  (ite true
    ($eo_typeof_main x1)
    eo.Stuck))))))))))) :named sm.axiom.$eo_typeof))

; fwd-decl: $eo_dt_constructors
(declare-fun $eo_dt_constructors (eo.Term) eo.Term)

; fwd-decl: $eo_dt_selectors
(declare-fun $eo_dt_selectors (eo.Term) eo.Term)

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
    ($eo_FunType x2 x2)
    eo.Stuck)))

; program: $eo_typeof_=
(define-fun $eo_typeof_= ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_FunType x1 (eo.SmtType tsm.Bool))
    eo.Stuck)))

; program: $eo_typeof_main
(assert (! (forall ((x1 eo.Term))
  (= ($eo_typeof_main x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite (= x1 eo.Type)
    eo.Type
  (ite ((_ is eo.FunType) x1)
    ($eo_requires ($eo_typeof (eo.FunType.arg1 x1)) eo.Type ($eo_requires ($eo_typeof (eo.FunType.arg2 x1)) eo.Type eo.Type))
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
    ($eo_FunType eo.Type eo.Type)
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Apply) (eo.SmtTerm.arg1 x1)) ((_ is sm.Apply) (sm.Apply.arg1 (eo.SmtTerm.arg1 x1))) (= (sm.Apply.arg1 (sm.Apply.arg1 (eo.SmtTerm.arg1 x1))) sm.ite))
    ($eo_typeof_ite ($eo_typeof (eo.SmtTerm (sm.Apply.arg2 (sm.Apply.arg1 (eo.SmtTerm.arg1 x1))))) ($eo_typeof (eo.SmtTerm (sm.Apply.arg2 (eo.SmtTerm.arg1 x1)))))
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.not))
    ($eo_FunType (eo.SmtType tsm.Bool) (eo.SmtType tsm.Bool))
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.and))
    ($eo_FunType (eo.SmtType tsm.Bool) ($eo_FunType (eo.SmtType tsm.Bool) (eo.SmtType tsm.Bool)))
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Apply) (eo.SmtTerm.arg1 x1)) (= (sm.Apply.arg1 (eo.SmtTerm.arg1 x1)) sm.=))
    ($eo_typeof_= ($eo_typeof (eo.SmtTerm (sm.Apply.arg2 (eo.SmtTerm.arg1 x1)))))
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.BitVec))
    ($eo_FunType (eo.SmtType tsm.Int) eo.Type)
  (ite ((_ is eo.Apply) x1)
    ($eo_typeof_apply ($eo_typeof (eo.Apply.arg1 x1)) ($eo_typeof (eo.Apply.arg2 x1)))
    eo.Stuck)))))))))))))))))) :named sm.axiom.$eo_typeof_main))

; program: $eo_dt_constructors
(assert (! (forall ((x1 eo.Term))
  (= ($eo_dt_constructors x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_requires (eo.SmtTerm sm.True) (eo.SmtTerm sm.False) (eo.SmtTerm sm.True))
    eo.Stuck)))) :named sm.axiom.$eo_dt_constructors))

; program: $eo_dt_selectors
(assert (! (forall ((x1 eo.Term))
  (= ($eo_dt_selectors x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_requires (eo.SmtTerm sm.True) (eo.SmtTerm sm.False) (eo.SmtTerm sm.True))
    eo.Stuck)))) :named sm.axiom.$eo_dt_selectors))

; fwd-decl: $eo_model_sat
(declare-fun $eo_model_sat (eo.Term) eo.Term)

; program: $eo_is_value
(define-fun $eo_is_value ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite true
    eo.Stuck
    eo.Stuck)))

; program: $eo_const_predicate
(define-fun $eo_const_predicate ((x1 Int) (x2 Int) (x3 eo.Term) (x4 eo.Term)) eo.Term
  (ite (or (= x3 eo.Stuck) (= x4 eo.Stuck))
    eo.Stuck
  (ite true
    eo.Stuck
    eo.Stuck)))

; program: $eo_model_eval
(define-fun $eo_model_eval ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    eo.Stuck
    eo.Stuck)))

; fwd-decl: $smtx_is_value
(declare-fun $smtx_is_value (tsm.Type sm.Term) Bool)

; fwd-decl: $smtx_typeof
(declare-fun $smtx_typeof (sm.Term) tsm.Type)

; program: $smtx_dt_is_value
(declare-fun $smtx_dt_is_value (sm.Term) Bool)
(assert (! (forall ((x1 sm.Term))
  (= ($smtx_dt_is_value x1)
  (ite ((_ is sm.Apply) x1)
    (ite ($smtx_is_value ($smtx_typeof (sm.Apply.arg2 x1)) (sm.Apply.arg2 x1)) ($smtx_dt_is_value (sm.Apply.arg1 x1)) false)
    (= ($eo_is_ok ($eo_dt_selectors (eo.SmtTerm x1))) (eo.SmtTerm sm.True))
))) :named sm.axiom.$smtx_dt_is_value))

; program: $smtx_is_value
(assert (! (forall ((x1 tsm.Type) (x2 sm.Term))
  (= ($smtx_is_value x1 x2)
  (ite (= x1 tsm.NullSort)
    false
  (ite ((_ is tsm.USort) x1)
    true
  (ite (and (= x1 tsm.Bool) (= x2 sm.True))
    true
  (ite (and (= x1 tsm.Bool) (= x2 sm.False))
    true
    (ite (= ($eo_is_ok ($eo_dt_constructors (eo.SmtType x1))) (eo.SmtTerm sm.True)) ($smtx_dt_is_value x2) (= sm.True (eo.SmtTerm.arg1 (ite ((_ is eo.SmtTerm) ($eo_is_value (eo.SmtType x1) (eo.SmtTerm x2))) ($eo_is_value (eo.SmtType x1) (eo.SmtTerm x2)) (eo.SmtTerm sm.False)))))
)))))) :named sm.axiom.$smtx_is_value))

; fwd-decl: $smtx_model_eval
(declare-fun $smtx_model_eval (sm.Term) sm.Term)

; fwd-decl: $smtx_model_lookup
(declare-fun $smtx_model_lookup (Int Int tsm.Type) sm.Term)

; program: $smtx_const_predicate
(define-fun $smtx_const_predicate ((x1 Int) (x2 Int) (x3 tsm.Type) (x4 sm.Term)) Bool
    (= (eo.SmtTerm.arg1 (ite ((_ is eo.SmtTerm) ($eo_const_predicate x1 x2 (eo.SmtType x3) (eo.SmtTerm x4))) ($eo_const_predicate x1 x2 (eo.SmtType x3) (eo.SmtTerm x4)) (eo.SmtTerm sm.True))) sm.True)
)

; program: $smtx_model_eval
(assert (! (forall ((x1 sm.Term))
  (= ($smtx_model_eval x1)
  (ite (= x1 sm.True)
    sm.True
  (ite (= x1 sm.False)
    sm.False
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) ((_ is sm.Apply) (sm.Apply.arg1 (sm.Apply.arg1 x1))) (= (sm.Apply.arg1 (sm.Apply.arg1 (sm.Apply.arg1 x1))) sm.ite))
    (ite (= ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 (sm.Apply.arg1 x1)))) sm.True) ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) (= (sm.Apply.arg1 (sm.Apply.arg1 x1)) sm.=))
    (ite (and ($smtx_is_value ($smtx_typeof (sm.Apply.arg2 (sm.Apply.arg1 x1))) (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_is_value ($smtx_typeof (sm.Apply.arg2 (sm.Apply.arg1 x1))) (sm.Apply.arg2 x1))) (ite (= (sm.Apply.arg2 (sm.Apply.arg1 x1)) (sm.Apply.arg2 x1)) sm.True sm.False) (sm.Apply (sm.Apply sm.= (sm.Apply.arg2 (sm.Apply.arg1 x1))) (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) (= (sm.Apply.arg1 x1) sm.not))
    (ite (or (= ($smtx_model_eval (sm.Apply.arg2 x1)) sm.True) (= ($smtx_model_eval (sm.Apply.arg2 x1)) sm.False)) (ite (not (= sm.True ($smtx_model_eval (sm.Apply.arg2 x1)))) sm.True sm.False) (sm.Apply sm.not (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) (= (sm.Apply.arg1 (sm.Apply.arg1 x1)) sm.and))
    (ite (and (or (= ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))) sm.True) (= ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))) sm.False)) (or (= ($smtx_model_eval (sm.Apply.arg2 x1)) sm.True) (= ($smtx_model_eval (sm.Apply.arg2 x1)) sm.False))) (ite (and (= sm.True ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1)))) (= sm.True ($smtx_model_eval (sm.Apply.arg2 x1)))) sm.True sm.False) (sm.Apply (sm.Apply sm.and (sm.Apply.arg2 (sm.Apply.arg1 x1))) (sm.Apply.arg2 x1)))
  (ite ((_ is sm.Const) x1)
    ($smtx_model_lookup 0 (sm.Const.arg2 x1) (sm.Const.arg1 x1))
    (eo.SmtTerm.arg1 (ite ((_ is eo.SmtTerm) ($eo_model_eval (eo.SmtTerm x1))) ($eo_model_eval (eo.SmtTerm x1)) (eo.SmtTerm x1)))
))))))))) :named sm.axiom.$smtx_model_eval))

; program: $eo_model_sat_internal
(define-fun $eo_model_sat_internal ((x1 sm.Term)) eo.Term
  (ite false
    eo.Stuck
  (ite (= x1 sm.True)
    (eo.SmtTerm sm.True)
  (ite true
    (eo.SmtTerm sm.False)
    eo.Stuck))))

; program: $eo_model_sat
(assert (! (forall ((x1 eo.Term))
  (= ($eo_model_sat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite ((_ is eo.SmtTerm) x1)
    ($eo_model_sat_internal ($smtx_model_eval (eo.SmtTerm.arg1 x1)))
    eo.Stuck)))) :named sm.axiom.$eo_model_sat))

; program: $smtx_typeof
(assert (! (forall ((x1 sm.Term))
  (= ($smtx_typeof x1)
  (ite ((_ is sm.Const) x1)
    (sm.Const.arg1 x1)
  (ite ((_ is sm.Skolem) x1)
    (sm.Skolem.arg1 x1)
    (eo.SmtType.arg1 (ite ((_ is eo.SmtType) ($eo_typeof (eo.SmtTerm x1))) ($eo_typeof (eo.SmtTerm x1)) (eo.SmtType tsm.NullSort)))
)))) :named sm.axiom.$smtx_typeof))

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
  (=> (or
        ; free constants always can be assumed to be a value
        (= i 0)
        ; skolems can be assumed to be a value if their predicate is satisfied
        ($smtx_const_predicate k i T ($smtx_model_lookup k i T)))
      ($smtx_is_value T ($smtx_model_lookup k i T))))
 :named sm.model_is_value))

;;; The verification condition

;;;; final verification condition for $eovc_symm
(assert (! (exists ((x1 sm.Term))
  (= ($eovc_symm (eo.SmtTerm x1)) (eo.SmtTerm sm.True))) :named sm.conjecture.$eovc_symm))


(check-sat)
