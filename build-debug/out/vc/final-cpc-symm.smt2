(set-logic UFDTSNIRA)
; This is both a valid *.smt2 and *.eo file after filling in the templates.
; For consistency we name it *.eo.

; tsm.Type:
;   The final embedding of SMT-LIB types that are relevant to the VC.
; sm.Term:
;   The final embedding of SMT-LIB terms that are relevant to the VC.
;   In other words, this defines the Herbrand universe.
; eo.Term:
;   The final embedding of Eunoia terms that are relevant to the VC.
;   SMT-LIB terms, types and values are embedded in this datatype.
;   We require a mutually recursive datatype, since these are
;   inter-dependent.
(declare-datatypes ((tsm.Type 0) (sm.Term 0) (eo.Term 0) (vsm.Value 0) (msm.Map 0))
  (
  (
  ; user-decl: Int
  (tsm.Int)
  ; user-decl: Real
  (tsm.Real)
  ; user-decl: Char
  (tsm.Char)
  ; user-decl: Seq
  (tsm.Seq)
  ; smt-cons: Bool
  (tsm.Bool)
  ; smt-cons: FunType
  (tsm.FunType (tsm.FunType.arg1 tsm.Type) (tsm.FunType.arg2 tsm.Type))
  ; smt-cons: USort
  (tsm.USort (tsm.USort.arg1 Int))
  ; smt-cons: NullSort
  (tsm.NullSort (tsm.NullSort.arg1 Int))
  ; user-decl: BitVec
  (tsm.BitVec)

  )
  (
  ; smt-cons: Bool
  (sm.Bool (sm.Bool.arg1 Bool))
  ; smt-cons: Numeral
  (sm.Numeral (sm.Numeral.arg1 Int))
  ; smt-cons: Rational
  (sm.Rational (sm.Rational.arg1 Real))
  ; smt-cons: String
  (sm.String (sm.String.arg1 String))
  ; smt-cons: Binary
  (sm.Binary (sm.Binary.arg1 Int) (sm.Binary.arg2 Int))
  ; smt-cons: Const
  (sm.Const (sm.Const.arg1 vsm.Value))
  ; user-decl: not
  (sm.not)
  ; user-decl: and
  (sm.and)
  ; user-decl: ite
  (sm.ite)
  ; user-decl: =
  (sm.=)

  )
  (
  ; smt-cons: Type
  (eo.Type)
  ; smt-cons: Stuck
  (eo.Stuck)
  ; smt-cons: Apply
  (eo.Apply (eo.Apply.arg1 eo.Term) (eo.Apply.arg2 eo.Term))
  ; smt-cons: FunType
  (eo.FunType (eo.FunType.arg1 eo.Term) (eo.FunType.arg2 eo.Term))
  ; smt-cons: SmtTerm
  (eo.SmtTerm (eo.SmtTerm.arg1 sm.Term))
  ; smt-cons: SmtType
  (eo.SmtType (eo.SmtType.arg1 tsm.Type))
  ; smt-cons: SmtValue
  (eo.SmtValue (eo.SmtValue.arg1 vsm.Value))
  ; smt-cons: Var
  (eo.Var (eo.Var.arg1 String) (eo.Var.arg2 eo.Term))
  ; user-decl: $eo_List
  (eo.$eo_List)

  )
  (
  ; smt-cons: Map
  (vsm.Map (vsm.Map.arg1 tsm.Type) (vsm.Map.arg2 msm.Map))
  ; smt-cons: NotValue
  (vsm.NotValue)
  ; smt-cons: UConst
  (vsm.UConst (vsm.UConst.arg1 tsm.Type) (vsm.UConst.arg2 Int))
  ; smt-cons: Term
  (vsm.Term (vsm.Term.arg1 sm.Term))

  )
  (
  ; (msm.Map.cons i e M) maps i -> e, as well as mappings in M
  (msm.Map.cons (msm.Map.cons.arg1 vsm.Value) (msm.Map.cons.arg2 vsm.Value) (msm.Map.cons.arg3 msm.Map))
  ; (msm.Map.default e) maps all remaining elements in the sort to e
  (msm.Map.default (msm.Map.default.arg1 vsm.Value))
  ))
)

;;; Relevant definitions

; fwd-decl: $eo_typeof
(declare-fun $eo_typeof (eo.Term) eo.Term)

; program: $eo_requires_eq
(define-fun $eo_requires_eq ((x1 eo.Term) (x2 eo.Term) (x3 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck) (= x3 eo.Stuck))
    eo.Stuck
  (ite (= x2 x1)
    x3
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
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Bool) (eo.SmtTerm.arg1 x1)))
    (eo.SmtType tsm.Bool)
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Numeral) (eo.SmtTerm.arg1 x1)))
    (eo.SmtType tsm.Int)
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Rational) (eo.SmtTerm.arg1 x1)))
    (eo.SmtType tsm.Real)
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.String) (eo.SmtTerm.arg1 x1)))
    (eo.Apply (eo.SmtType tsm.Seq) (eo.SmtType tsm.Char))
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Binary) (eo.SmtTerm.arg1 x1)))
    eo.Type
  (ite ((_ is eo.Var) x1)
    (eo.Var.arg2 x1)
  (ite true
    ($eo_typeof_main x1)
    eo.Stuck)))))))))) :named sm.axiom.$eo_typeof))

; program: $mk_symm
(define-fun $mk_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 x1))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1))) sm.=))
    (eo.Apply (eo.Apply (eo.SmtTerm sm.=) (eo.Apply.arg2 x1)) (eo.Apply.arg2 (eo.Apply.arg1 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg2 x1)) ((_ is eo.Apply) (eo.Apply.arg1 (eo.Apply.arg2 x1))) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 (eo.Apply.arg2 x1)))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 (eo.Apply.arg2 x1)))) sm.=) ((_ is eo.SmtTerm) (eo.Apply.arg1 x1)) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 x1)) sm.not))
    (eo.Apply (eo.SmtTerm sm.not) (eo.Apply (eo.Apply (eo.SmtTerm sm.=) (eo.Apply.arg2 (eo.Apply.arg2 x1))) (eo.Apply.arg2 (eo.Apply.arg1 (eo.Apply.arg2 x1)))))
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
    (eo.FunType x2 x2)
    eo.Stuck)))

; program: $eo_typeof_=
(define-fun $eo_typeof_= ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (eo.FunType x1 (eo.SmtType tsm.Bool))
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
  (ite (= x1 (eo.SmtTerm (sm.Bool true)))
    (eo.SmtType tsm.Bool)
  (ite (= x1 (eo.SmtTerm (sm.Bool false)))
    (eo.SmtType tsm.Bool)
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.Int))
    eo.Type
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.Real))
    eo.Type
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.Char))
    eo.Type
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.Seq))
    (eo.FunType eo.Type eo.Type)
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 x1))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1))) sm.ite))
    ($eo_typeof_ite ($eo_typeof (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($eo_typeof (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.not))
    (eo.FunType (eo.SmtType tsm.Bool) (eo.SmtType tsm.Bool))
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.and))
    (eo.FunType (eo.SmtType tsm.Bool) (eo.FunType (eo.SmtType tsm.Bool) (eo.SmtType tsm.Bool)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.SmtTerm) (eo.Apply.arg1 x1)) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 x1)) sm.=))
    ($eo_typeof_= ($eo_typeof (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.BitVec))
    (eo.FunType (eo.SmtType tsm.Int) eo.Type)
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

; fwd-decl: $smtx_map_is_value
(declare-fun $smtx_map_is_value (tsm.Type msm.Map) Bool)

; program: $smtx_term_is_value
(assert (! (forall ((x1 sm.Term))
  (= ($smtx_term_is_value x1)
  (ite ((_ is sm.Bool) x1)
    true
  (ite ((_ is sm.Numeral) x1)
    true
  (ite ((_ is sm.Rational) x1)
    true
  (ite ((_ is sm.String) x1)
    true
    false
)))))) :named sm.axiom.$smtx_term_is_value))

; program: $smtx_ensure_value
(define-fun $smtx_ensure_value ((x1 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Term) x1)
    (ite ($smtx_term_is_value (vsm.Term.arg1 x1)) (vsm.Term (vsm.Term.arg1 x1)) vsm.NotValue)
  (ite ((_ is vsm.Map) x1)
    (ite ($smtx_map_is_value (vsm.Map.arg1 x1) (vsm.Map.arg2 x1)) (vsm.Map (vsm.Map.arg1 x1) (vsm.Map.arg2 x1)) vsm.NotValue)
  (ite ((_ is vsm.UConst) x1)
    (vsm.UConst (vsm.UConst.arg1 x1) (vsm.UConst.arg2 x1))
    vsm.NotValue
))))

; fwd-decl: $smtx_model_eval
(declare-fun $smtx_model_eval (eo.Term) vsm.Value)

; fwd-decl: $smtx_model_lookup
(declare-fun $smtx_model_lookup (sm.Term) vsm.Value)

; program: $smtx_model_lookup_predicate_internal
(define-fun $smtx_model_lookup_predicate_internal ((x1 sm.Term) (x2 vsm.Value)) Bool
    true
)

; program: $smtx_model_lookup_predicate
(define-fun $smtx_model_lookup_predicate ((x1 sm.Term)) Bool
    ($smtx_model_lookup_predicate_internal x1 ($smtx_model_lookup x1))
)

; program: $smtx_model_eval_apply
(define-fun $smtx_model_eval_apply ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Map) x1)
    ($smtx_map_lookup (vsm.Map.arg2 x1) x2)
    vsm.NotValue
))

; program: $smtx_model_eval_ite
(define-fun $smtx_model_eval_ite ((x1 vsm.Value) (x2 vsm.Value) (x3 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)) (= (sm.Bool.arg1 (vsm.Term.arg1 x1)) true))
    x2
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)) (= (sm.Bool.arg1 (vsm.Term.arg1 x1)) false))
    x3
    vsm.NotValue
)))

; program: $smtx_model_eval_=
(define-fun $smtx_model_eval_= ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite (= x1 vsm.NotValue)
    vsm.NotValue
  (ite (= x2 vsm.NotValue)
    vsm.NotValue
    (vsm.Term (sm.Bool (= x1 x2)))
)))

; program: $smtx_model_eval_not
(define-fun $smtx_model_eval_not ((x1 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)))
    (vsm.Term (sm.Bool (not (sm.Bool.arg1 (vsm.Term.arg1 x1)))))
    vsm.NotValue
))

; program: $smtx_model_eval_and
(define-fun $smtx_model_eval_and ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)) ((_ is vsm.Term) x2) ((_ is sm.Bool) (vsm.Term.arg1 x2)))
    (vsm.Term (sm.Bool (and (sm.Bool.arg1 (vsm.Term.arg1 x1)) (sm.Bool.arg1 (vsm.Term.arg1 x2)))))
    vsm.NotValue
))

; program: $smtx_model_eval
(assert (! (forall ((x1 eo.Term))
  (= ($smtx_model_eval x1)
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.Apply) (eo.Apply.arg1 (eo.Apply.arg1 x1))) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1)))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1)))) sm.ite))
    ($smtx_model_eval_ite ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 (eo.Apply.arg1 x1)))) ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 x1))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1))) sm.=))
    ($smtx_model_eval_= ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.SmtTerm) (eo.Apply.arg1 x1)) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 x1)) sm.not))
    ($smtx_model_eval_not ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 x1))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1))) sm.and))
    ($smtx_model_eval_and ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Const) (eo.SmtTerm.arg1 x1)))
    ($smtx_ensure_value (sm.Const.arg1 (eo.SmtTerm.arg1 x1)))
  (ite ((_ is eo.Apply) x1)
    ($smtx_model_eval_apply ($smtx_model_eval (eo.Apply.arg1 x1)) ($smtx_model_eval (eo.Apply.arg2 x1)))
    ($smtx_ensure_value (vsm.Term (eo.SmtTerm.arg1 x1)))
)))))))) :named sm.axiom.$smtx_model_eval))

; program: $eo_model_sat_internal
(define-fun $eo_model_sat_internal ((x1 vsm.Value)) eo.Term
  (ite false
    eo.Stuck
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)) (= (sm.Bool.arg1 (vsm.Term.arg1 x1)) true))
    (eo.SmtTerm (sm.Bool true))
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)) (= (sm.Bool.arg1 (vsm.Term.arg1 x1)) false))
    (eo.SmtTerm (sm.Bool false))
    eo.Stuck))))

; program: $eo_model_sat
(assert (! (forall ((x1 eo.Term))
  (= ($eo_model_sat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_model_sat_internal ($smtx_model_eval x1))
    eo.Stuck)))) :named sm.axiom.$eo_model_sat))

; program: $eor_symm
(define-fun $eor_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($mk_symm x1)
    eo.Stuck)))

; program: $eovc_symm
(define-fun $eovc_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_requires_eq ($eo_model_sat x1) (eo.SmtTerm (sm.Bool true)) ($eo_requires_eq ($eo_model_sat ($eor_symm x1)) (eo.SmtTerm (sm.Bool false)) (eo.SmtTerm (sm.Bool true))))
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

; This axiom gives semantics to model lookups for partial functions
(assert (! (forall ((t sm.Term))
  ($smtx_model_lookup_predicate t))
  :named sm.model_lookup_predicate))

;;; The verification condition

;;;; final verification condition for $eovc_symm
(assert (! (exists ((x1 eo.Term))
  (= ($eovc_symm x1) (eo.SmtTerm (sm.Bool true)))) :named sm.conjecture.$eovc_symm))


(check-sat)
