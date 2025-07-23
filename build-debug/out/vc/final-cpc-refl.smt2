(set-logic UFDTSNIRA)

; tsm.Type:
;   The final embedding of atomic SMT-LIB types that are relevant to the VC.
; sm.Term:
;   The final embedding of atomic SMT-LIB terms that are relevant to the VC.
; eo.Term:
;   The final embedding of Eunoia terms that are relevant to the VC.
;   SMT-LIB terms, types and values are embedded in this datatype. This
;   datatype contains a superset of the Herbrand universe of all types being
;   considered.
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
  ; user-decl: ite
  (sm.ite)
  ; user-decl: and
  (sm.and)
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
  (eo.FunType)
  ; smt-cons: SmtTerm
  (eo.SmtTerm (eo.SmtTerm.arg1 sm.Term))
  ; smt-cons: SmtType
  (eo.SmtType (eo.SmtType.arg1 tsm.Type))
  ; smt-cons: Var
  (eo.Var (eo.Var.arg1 String) (eo.Var.arg2 Int))
  ; user-decl: $eo_List
  (eo.$eo_List)
  ; user-decl: $eo_List_nil
  (eo.$eo_List_nil)
  ; user-decl: $eo_List_cons
  (eo.$eo_List_cons)

  )
  (
  ; smt-cons: Map
  (vsm.Map (vsm.Map.arg1 Int) (vsm.Map.arg2 msm.Map))
  ; smt-cons: UConst
  (vsm.UConst (vsm.UConst.arg1 Int) (vsm.UConst.arg2 Int))
  ; smt-cons: Term
  (vsm.Term (vsm.Term.arg1 sm.Term))
  ; smt-cons: Apply
  (vsm.Apply (vsm.Apply.arg1 vsm.Value) (vsm.Apply.arg2 vsm.Value))
  ; smt-cons: NotValue
  (vsm.NotValue)

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

; program: $eo_fail_prog
(define-fun $eo_fail_prog ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite (= x1 (eo.SmtTerm (sm.Bool true)))
    (eo.SmtTerm (sm.Bool true))
    eo.Stuck)))

; program: $eo_if_both
(define-fun $eo_if_both ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite (and (= x1 (eo.SmtTerm (sm.Bool true))) (= x2 (eo.SmtTerm (sm.Bool true))))
    (eo.SmtTerm (sm.Bool true))
  (ite true
    (eo.SmtTerm (sm.Bool false))
    eo.Stuck))))

; program: $eo_requires_eq
(define-fun $eo_requires_eq ((x1 eo.Term) (x2 eo.Term) (x3 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck) (= x3 eo.Stuck))
    eo.Stuck
  (ite (= x2 x1)
    x3
    eo.Stuck)))

; fwd-decl: $eo_hash
(declare-fun $eo_hash (eo.Term) eo.Term)

; fwd-decl: $eo_reverse_hash
(declare-fun $eo_reverse_hash (eo.Term) eo.Term)

; fwd-decl: $eo_typeof_main
(declare-fun $eo_typeof_main (eo.Term) eo.Term)

; program: $eo_typeof
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_typeof x1)
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
    ($eo_reverse_hash (eo.SmtTerm (sm.Numeral (eo.Var.arg2 x1))))
  (ite true
    ($eo_typeof_main x1)
    eo.Stuck))))))))) :pattern (($eo_typeof x1)))) :named sm.axiom.$eo_typeof))

; program: $eo_typeof_apply
(define-fun $eo_typeof_apply ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.FunType) (eo.Apply.arg1 (eo.Apply.arg1 x1))) (= x2 (eo.Apply.arg2 (eo.Apply.arg1 x1))))
    (eo.Apply.arg2 x1)
    eo.Stuck)))

; program: $eo_typeof_ite
(define-fun $eo_typeof_ite ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite (= x1 (eo.SmtType tsm.Bool))
    (eo.Apply (eo.Apply eo.FunType x2) x2)
    eo.Stuck)))

; program: $eo_typeof_=
(define-fun $eo_typeof_= ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (eo.Apply (eo.Apply eo.FunType x1) (eo.SmtType tsm.Bool))
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
  (! (= ($eo_typeof_main x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite (= x1 eo.Type)
    eo.Type
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.FunType) (eo.Apply.arg1 (eo.Apply.arg1 x1))))
    ($eo_typeof_fun_type ($eo_typeof (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($eo_typeof (eo.Apply.arg2 x1)))
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
    (eo.Apply (eo.Apply eo.FunType eo.Type) eo.Type)
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 x1))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1))) sm.ite))
    ($eo_typeof_ite ($eo_typeof (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($eo_typeof (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.SmtTerm) x1) (= (eo.SmtTerm.arg1 x1) sm.and))
    (eo.Apply (eo.Apply eo.FunType (eo.SmtType tsm.Bool)) (eo.Apply (eo.Apply eo.FunType (eo.SmtType tsm.Bool)) (eo.SmtType tsm.Bool)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.SmtTerm) (eo.Apply.arg1 x1)) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 x1)) sm.=))
    ($eo_typeof_= ($eo_typeof (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.SmtType) x1) (= (eo.SmtType.arg1 x1) tsm.BitVec))
    (eo.Apply (eo.Apply eo.FunType (eo.SmtType tsm.Int)) eo.Type)
  (ite ((_ is eo.Apply) x1)
    ($eo_typeof_apply ($eo_typeof (eo.Apply.arg1 x1)) ($eo_typeof (eo.Apply.arg2 x1)))
    eo.Stuck)))))))))))))))) :pattern (($eo_typeof_main x1)))) :named sm.axiom.$eo_typeof_main))

; program: $eo_dt_selectors
(define-fun $eo_dt_selectors ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_fail_prog (eo.SmtTerm (sm.Bool false)))
    eo.Stuck)))

; fwd-decl: $eo_model_sat
(declare-fun $eo_model_sat (eo.Term) eo.Term)

; fwd-decl: $eo_model_is_input
(declare-fun $eo_model_is_input (eo.Term) eo.Term)

; fwd-decl: $smtx_is_value
(declare-fun $smtx_is_value (vsm.Value) Bool)

; program: $smtx_map_lookup
(declare-fun $smtx_map_lookup (msm.Map vsm.Value) vsm.Value)
(assert (! (forall ((x1 msm.Map) (x2 vsm.Value))
  (! (= ($smtx_map_lookup x1 x2)
  (ite (and ((_ is msm.Map.cons) x1) (= x2 (msm.Map.cons.arg1 x1)))
    (msm.Map.cons.arg2 x1)
  (ite ((_ is msm.Map.cons) x1)
    ($smtx_map_lookup (msm.Map.cons.arg3 x1) x2)
    (msm.Map.default.arg1 x1)
))) :pattern (($smtx_map_lookup x1 x2)))) :named sm.axiom.$smtx_map_lookup))

; fwd-decl: $smtx_map_is_value
(declare-fun $smtx_map_is_value (Int msm.Map) Bool)

; program: $smtx_term_is_value
(define-fun $smtx_term_is_value ((x1 sm.Term)) Bool
  (ite ((_ is sm.Bool) x1)
    true
  (ite ((_ is sm.Numeral) x1)
    true
  (ite ((_ is sm.Rational) x1)
    true
  (ite ((_ is sm.String) x1)
    true
    false
)))))

; program: $smtx_is_value
(assert (! (forall ((x1 vsm.Value))
  (! (= ($smtx_is_value x1)
  (ite ((_ is vsm.Term) x1)
    ($smtx_term_is_value (vsm.Term.arg1 x1))
  (ite ((_ is vsm.Map) x1)
    ($smtx_map_is_value (vsm.Map.arg1 x1) (vsm.Map.arg2 x1))
  (ite ((_ is vsm.UConst) x1)
    true
  (ite (and ((_ is vsm.Apply) x1) (= (vsm.Apply.arg2 x1) vsm.NotValue) ((_ is vsm.Term) (vsm.Apply.arg1 x1)))
    (not (= ($eo_dt_selectors (eo.SmtTerm (vsm.Term.arg1 (vsm.Apply.arg1 x1)))) eo.Stuck))
  (ite ((_ is vsm.Apply) x1)
    (and ($smtx_is_value (vsm.Apply.arg1 x1)) ($smtx_is_value (vsm.Apply.arg2 x1)))
    false
)))))) :pattern (($smtx_is_value x1)))) :named sm.axiom.$smtx_is_value))

; program: $smtx_ensure_value
(define-fun $smtx_ensure_value ((x1 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Term) x1)
    (ite ($smtx_term_is_value (vsm.Term.arg1 x1)) (vsm.Term (vsm.Term.arg1 x1)) (ite (not (= ($eo_dt_selectors (eo.SmtTerm (vsm.Term.arg1 x1))) eo.Stuck)) (vsm.Apply (vsm.Term (vsm.Term.arg1 x1)) vsm.NotValue) vsm.NotValue))
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
  (ite ((_ is vsm.Apply) x1)
    (vsm.Apply (vsm.Apply (vsm.Apply.arg1 x1) (vsm.Apply.arg2 x1)) x2)
  (ite ((_ is vsm.Map) x1)
    ($smtx_map_lookup (vsm.Map.arg2 x1) x2)
    vsm.NotValue
)))

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

; program: $smtx_model_eval_and
(define-fun $smtx_model_eval_and ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)) ((_ is vsm.Term) x2) ((_ is sm.Bool) (vsm.Term.arg1 x2)))
    (vsm.Term (sm.Bool (and (sm.Bool.arg1 (vsm.Term.arg1 x1)) (sm.Bool.arg1 (vsm.Term.arg1 x2)))))
    vsm.NotValue
))

; program: $smtx_model_eval
(assert (! (forall ((x1 eo.Term))
  (! (= ($smtx_model_eval x1)
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.Apply) (eo.Apply.arg1 (eo.Apply.arg1 x1))) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1)))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1)))) sm.ite))
    ($smtx_model_eval_ite ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 (eo.Apply.arg1 x1)))) ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 x1))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1))) sm.=))
    ($smtx_model_eval_= ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.SmtTerm) (eo.Apply.arg1 (eo.Apply.arg1 x1))) (= (eo.SmtTerm.arg1 (eo.Apply.arg1 (eo.Apply.arg1 x1))) sm.and))
    ($smtx_model_eval_and ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Const) (eo.SmtTerm.arg1 x1)))
    ($smtx_ensure_value (sm.Const.arg1 (eo.SmtTerm.arg1 x1)))
  (ite ((_ is eo.Apply) x1)
    ($smtx_model_eval_apply ($smtx_model_eval (eo.Apply.arg1 x1)) ($smtx_model_eval (eo.Apply.arg2 x1)))
    (ite ($smtx_term_is_value (eo.SmtTerm.arg1 x1)) (vsm.Term (eo.SmtTerm.arg1 x1)) (ite (not (= ($eo_dt_selectors x1) eo.Stuck)) (vsm.Apply (vsm.Term (eo.SmtTerm.arg1 x1)) vsm.NotValue) vsm.NotValue))
)))))) :pattern (($smtx_model_eval x1)))) :named sm.axiom.$smtx_model_eval))

; program: $smtx_model_sat
(define-fun $smtx_model_sat ((x1 vsm.Value)) eo.Term
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)) (= (sm.Bool.arg1 (vsm.Term.arg1 x1)) true))
    (eo.Apply (eo.Apply eo.$eo_List_cons (eo.SmtTerm (sm.Bool true))) (eo.Apply (eo.Apply eo.$eo_List_cons eo.$eo_List_nil) eo.$eo_List_nil))
  (ite (and ((_ is vsm.Term) x1) ((_ is sm.Bool) (vsm.Term.arg1 x1)) (= (sm.Bool.arg1 (vsm.Term.arg1 x1)) false))
    (eo.Apply (eo.Apply eo.$eo_List_cons (eo.SmtTerm (sm.Bool false))) (eo.Apply (eo.Apply eo.$eo_List_cons eo.$eo_List_nil) eo.$eo_List_nil))
    eo.$eo_List_nil
)))

; program: $smtx_is_input
(declare-fun $smtx_is_input (eo.Term) eo.Term)
(assert (! (forall ((x1 eo.Term))
  (! (= ($smtx_is_input x1)
  (ite ((_ is eo.Apply) x1)
    ($eo_if_both ($smtx_is_input (eo.Apply.arg1 x1)) ($smtx_is_input (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.SmtTerm) x1) ((_ is sm.Const) (eo.SmtTerm.arg1 x1)))
    (eo.SmtTerm (sm.Bool ($smtx_is_value (sm.Const.arg1 (eo.SmtTerm.arg1 x1)))))
  (ite ((_ is eo.SmtTerm) x1)
    (eo.SmtTerm (sm.Bool true))
  (ite ((_ is eo.SmtType) x1)
    (eo.SmtTerm (sm.Bool true))
    (eo.SmtTerm (sm.Bool false))
))))) :pattern (($smtx_is_input x1)))) :named sm.axiom.$smtx_is_input))

; program: $eo_model_sat
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_model_sat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($smtx_model_sat ($smtx_model_eval x1))
    eo.Stuck))) :pattern (($eo_model_sat x1)))) :named sm.axiom.$eo_model_sat))

; program: $eo_model_is_input
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_model_is_input x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($smtx_is_input x1)
    eo.Stuck))) :pattern (($eo_model_is_input x1)))) :named sm.axiom.$eo_model_is_input))

; program: $eor_refl
(define-fun $eor_refl ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (eo.Apply (eo.Apply (eo.SmtTerm sm.=) x1) x1)
    eo.Stuck)))

; program: $eovc_refl
(define-fun $eovc_refl ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_requires_eq ($eo_model_is_input ($eor_refl x1)) (eo.SmtTerm (sm.Bool true)) ($eo_requires_eq ($eo_model_sat ($eor_refl x1)) (eo.Apply (eo.Apply eo.$eo_List_cons (eo.SmtTerm (sm.Bool false))) (eo.Apply (eo.Apply eo.$eo_List_cons eo.$eo_List_nil) eo.$eo_List_nil)) (eo.SmtTerm (sm.Bool true))))
    eo.Stuck)))



;;; Meta-level properties of models

; axiom: $eo_hash
; note: This is defined axiomatically.
(assert (! (forall ((x eo.Term))
  (=> (not (= x eo.Stuck))
    (and
      ((_ is eo.SmtTerm) ($eo_hash x))
      ((_ is sm.Numeral) (eo.SmtTerm.arg1 ($eo_hash x)))))) :named sm.hash_numeral))
(assert (! (forall ((x eo.Term))
    (= ($eo_reverse_hash ($eo_hash x)) x)) :named sm.hash_injective))

; This axiom gives semantics to model lookups for partial functions
(assert (! (forall ((t sm.Term))
  ($smtx_model_lookup_predicate t))
  :named sm.model_lookup_predicate))

;;; The verification condition

;;;; final verification condition for $eovc_refl
(assert (! (exists ((x1 eo.Term))
  (= ($eovc_refl x1) (eo.SmtTerm (sm.Bool true)))) :named sm.conjecture.$eovc_refl))
(check-sat)

