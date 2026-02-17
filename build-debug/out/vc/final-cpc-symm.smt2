(set-logic ALL)

(define-sort Rat () Real)
; Helpers to avoid mixed arithmetic
(define-fun mk_rational ((x Int) (y Int)) Real (/ (to_real x) (to_real y)))
(define-fun zeq ((x Int) (y Int)) Bool (= x y))
(define-fun zleq ((x Int) (y Int)) Bool (<= x y))
(define-fun zlt ((x Int) (y Int)) Bool (< x y))
(define-fun zplus ((x Int) (y Int)) Int (+ x y))
(define-fun zmult ((x Int) (y Int)) Int (* x y))
(define-fun zneg ((x Int)) Int (- x))
(define-fun qeq ((x Real) (y Real)) Bool (= x y))
(define-fun qleq ((x Real) (y Real)) Bool (<= x y))
(define-fun qlt ((x Real) (y Real)) Bool (< x y))
(define-fun qplus ((x Real) (y Real)) Real (+ x y))
(define-fun qmult ((x Real) (y Real)) Real (* x y))
(define-fun qneg ((x Real)) Real (- x))

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
(declare-datatypes ((eo.Term 0) (vsm.Value 0) (msm.Map 0) (ssm.Seq 0))
  (
  (
  ; user-decl: $eo_Proof
  (eo.$eo_Proof)
  ; user-decl: $eo_pf
  (eo.$eo_pf (eo.$eo_pf.arg1 eo.Term))
  ; user-decl: Int
  (eo.Int)
  ; user-decl: Real
  (eo.Real)
  ; user-decl: BitVec
  (eo.BitVec)
  ; user-decl: Char
  (eo.Char)
  ; user-decl: Seq
  (eo.Seq)
  ; user-decl: $eo_List
  (eo.$eo_List)
  ; user-decl: $eo_List_nil
  (eo.$eo_List_nil)
  ; user-decl: $eo_List_cons
  (eo.$eo_List_cons)
  ; smt-cons: Bool
  (eo.Bool)
  ; smt-cons: Boolean
  (eo.Boolean (eo.Boolean.arg1 Bool))
  ; smt-cons: Numeral
  (eo.Numeral (eo.Numeral.arg1 Int))
  ; smt-cons: Rational
  (eo.Rational (eo.Rational.arg1 Rat))
  ; smt-cons: String
  (eo.String (eo.String.arg1 String))
  ; smt-cons: Binary
  (eo.Binary (eo.Binary.arg1 Int) (eo.Binary.arg2 Int))
  ; smt-cons: Type
  (eo.Type)
  ; smt-cons: Stuck
  (eo.Stuck)
  ; smt-cons: Apply
  (eo.Apply (eo.Apply.arg1 eo.Term) (eo.Apply.arg2 eo.Term))
  ; smt-cons: FunType
  (eo.FunType)
  ; smt-cons: Var
  (eo.Var (eo.Var.arg1 String) (eo.Var.arg2 eo.Term))
  ; user-decl: not
  (eo.not)
  ; user-decl: and
  (eo.and)
  ; user-decl: =
  (eo.=)

  )
  (
  ; smt-cons: Map
  (vsm.Map (vsm.Map.arg1 msm.Map))
  ; smt-cons: Term
  (vsm.Term (vsm.Term.arg1 eo.Term))
  ; smt-cons: Apply
  (vsm.Apply (vsm.Apply.arg1 vsm.Value) (vsm.Apply.arg2 vsm.Value))
  ; smt-cons: NotValue
  (vsm.NotValue)

  )
  (
  ; (msm.cons i e M) maps i -> e, as well as mappings in M
  (msm.cons (msm.cons.arg1 vsm.Value) (msm.cons.arg2 vsm.Value) (msm.cons.arg3 msm.Map))
  ; (msm.default e) maps all remaining elements in the sort to e
  (msm.default (msm.default.arg1 vsm.Value))
  )
  (
  ; (ssm.cons i s) is a sequence
  (ssm.cons (ssm.cons.arg1 vsm.Value) (ssm.cons.arg2 ssm.Seq))
  ; the empty sequence
  (ssm.empty)
  )
  )
)

;;; Relevant definitions

; program: $eo_proven
(define-fun $eo_proven ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite ((_ is eo.$eo_pf) x1)
    (eo.$eo_pf.arg1 x1)
    eo.Stuck)))

; fwd-decl: $eo_typeof
(declare-fun $eo_typeof (eo.Term) eo.Term)

; fwd-decl: $eo_dt_selectors
(declare-fun $eo_dt_selectors (eo.Term) eo.Term)

; program: $smtx_pow2
(declare-fun $smtx_pow2 (Int) Int)
(assert (! (forall ((x1 Int))
  (! (= ($smtx_pow2 x1)
    (ite (zleq x1 0) 1 (zmult 2 ($smtx_pow2 (zplus x1 (zneg 1)))))
) :pattern (($smtx_pow2 x1)))) :named sm.axiom.$smtx_pow2))

(define-fun $eo_Bool () eo.Term eo.Bool)
; program: $eo_bool
(define-fun $eo_bool ((x1 Bool)) eo.Term
    (eo.Boolean x1)
)

; program: $eo_numeral
(define-fun $eo_numeral ((x1 Int)) eo.Term
    (eo.Numeral x1)
)

; program: $eo_rational
(define-fun $eo_rational ((x1 Rat)) eo.Term
    (eo.Rational x1)
)

; program: $eo_string
(define-fun $eo_string ((x1 String)) eo.Term
    (eo.String x1)
)

; program: $eo_binary
(define-fun $eo_binary ((x1 Int) (x2 Int)) eo.Term
    (eo.Binary x1 x2)
)

(define-fun $eo_Type () eo.Term eo.Type)
(define-fun $eo_stuck () eo.Term eo.Stuck)
; program: $eo_apply
(define-fun $eo_apply ((x1 eo.Term) (x2 eo.Term)) eo.Term
    (eo.Apply x1 x2)
)

(define-fun $eo_fun_type () eo.Term eo.FunType)
; program: $eo_Var
(define-fun $eo_Var ((x1 String) (x2 eo.Term)) eo.Term
    (eo.Var x1 x2)
)

; program: $eo_binary_mod_w
(define-fun $eo_binary_mod_w ((x1 Int) (x2 Int)) eo.Term
    (eo.Binary x1 (mod x2 ($smtx_pow2 x1)))
)

; program: $eo_requires
(define-fun $eo_requires ((x1 eo.Term) (x2 eo.Term) (x3 eo.Term)) eo.Term
    (ite (= x1 x2) (ite (not (= x1 eo.Stuck)) x3 eo.Stuck) eo.Stuck)
)

; program: $eo_mk_apply
(define-fun $eo_mk_apply ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite true
    (eo.Apply x1 x2)
    eo.Stuck)))

; program: $eo_len
(define-fun $eo_len ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite ((_ is eo.String) x1)
    (eo.Numeral (str.len (eo.String.arg1 x1)))
  (ite ((_ is eo.Binary) x1)
    (eo.Numeral (eo.Binary.arg1 x1))
    eo.Stuck))))

; fwd-decl: $smtx_hash
(declare-fun $smtx_hash (eo.Term) Int)

; fwd-decl: $eo_reverse_hash
(declare-fun $eo_reverse_hash (Int) eo.Term)

; fwd-decl: $eo_typeof_main
(declare-fun $eo_typeof_main (eo.Term) eo.Term)

; fwd-decl: $eo_lit_type_Numeral
(declare-fun $eo_lit_type_Numeral (eo.Term) eo.Term)

; fwd-decl: $eo_lit_type_Rational
(declare-fun $eo_lit_type_Rational (eo.Term) eo.Term)

; fwd-decl: $eo_lit_type_Binary
(declare-fun $eo_lit_type_Binary (eo.Term) eo.Term)

; fwd-decl: $eo_lit_type_String
(declare-fun $eo_lit_type_String (eo.Term) eo.Term)

; program: $eo_typeof
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_typeof x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite ((_ is eo.Boolean) x1)
    eo.Bool
  (ite ((_ is eo.Numeral) x1)
    ($eo_lit_type_Numeral (eo.Numeral (eo.Numeral.arg1 x1)))
  (ite ((_ is eo.Rational) x1)
    ($eo_lit_type_Rational (eo.Rational (eo.Rational.arg1 x1)))
  (ite ((_ is eo.String) x1)
    ($eo_lit_type_String (eo.String (eo.String.arg1 x1)))
  (ite ((_ is eo.Binary) x1)
    ($eo_lit_type_Binary (eo.Binary (eo.Binary.arg1 x1) (eo.Binary.arg2 x1)))
  (ite ((_ is eo.Var) x1)
    (eo.Var.arg2 x1)
  (ite true
    ($eo_typeof_main x1)
    eo.Stuck))))))))) :pattern (($eo_typeof x1)))) :named sm.axiom.$eo_typeof))

; program: $mk_symm
(define-fun $mk_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) (= (eo.Apply.arg1 (eo.Apply.arg1 x1)) eo.=))
    (eo.Apply (eo.Apply eo.= (eo.Apply.arg2 x1)) (eo.Apply.arg2 (eo.Apply.arg1 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg2 x1)) ((_ is eo.Apply) (eo.Apply.arg1 (eo.Apply.arg2 x1))) (= (eo.Apply.arg1 (eo.Apply.arg1 (eo.Apply.arg2 x1))) eo.=) (= (eo.Apply.arg1 x1) eo.not))
    (eo.Apply eo.not (eo.Apply (eo.Apply eo.= (eo.Apply.arg2 (eo.Apply.arg2 x1))) (eo.Apply.arg2 (eo.Apply.arg1 (eo.Apply.arg2 x1)))))
    eo.Stuck))))

; program: $eo_prog_symm
(define-fun $eo_prog_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite ((_ is eo.$eo_pf) x1)
    ($mk_symm (eo.$eo_pf.arg1 x1))
    eo.Stuck)))

; program: $eo_typeof_apply
(define-fun $eo_typeof_apply ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.FunType) (eo.Apply.arg1 (eo.Apply.arg1 x1))))
    ($eo_requires (eo.Apply.arg2 (eo.Apply.arg1 x1)) x2 (eo.Apply.arg2 x1))
    eo.Stuck)))

; program: $eo_typeof_=
(define-fun $eo_typeof_= ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (eo.Apply (eo.Apply eo.FunType x1) eo.Bool)
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
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.FunType) (eo.Apply.arg1 (eo.Apply.arg1 x1))))
    ($eo_typeof_fun_type ($eo_typeof (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($eo_typeof (eo.Apply.arg2 x1)))
  (ite (= x1 eo.Bool)
    eo.Type
  (ite (= x1 (eo.Boolean true))
    eo.Bool
  (ite (= x1 (eo.Boolean false))
    eo.Bool
  (ite (= x1 eo.$eo_List)
    eo.Type
  (ite (= x1 eo.$eo_List_nil)
    eo.$eo_List
  (ite (and ((_ is eo.Apply) x1) (= (eo.Apply.arg1 x1) eo.$eo_List_cons))
    (eo.Apply (eo.Apply eo.FunType eo.$eo_List) eo.$eo_List)
  (ite (= x1 eo.Int)
    eo.Type
  (ite (= x1 eo.Real)
    eo.Type
  (ite (= x1 eo.BitVec)
    (eo.Apply (eo.Apply eo.FunType eo.Int) eo.Type)
  (ite (= x1 eo.Char)
    eo.Type
  (ite (= x1 eo.Seq)
    (eo.Apply (eo.Apply eo.FunType eo.Type) eo.Type)
  (ite (= x1 eo.not)
    (eo.Apply (eo.Apply eo.FunType eo.Bool) eo.Bool)
  (ite (= x1 eo.and)
    (eo.Apply (eo.Apply eo.FunType eo.Bool) (eo.Apply (eo.Apply eo.FunType eo.Bool) eo.Bool))
  (ite (and ((_ is eo.Apply) x1) (= (eo.Apply.arg1 x1) eo.=))
    ($eo_typeof_= ($eo_typeof (eo.Apply.arg2 x1)))
  (ite ((_ is eo.Apply) x1)
    ($eo_typeof_apply ($eo_typeof (eo.Apply.arg1 x1)) ($eo_typeof (eo.Apply.arg2 x1)))
    eo.Stuck))))))))))))))))))) :pattern (($eo_typeof_main x1)))) :named sm.axiom.$eo_typeof_main))

; program: $eo_lit_type_Numeral
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_lit_type_Numeral x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    eo.Int
    eo.Stuck))) :pattern (($eo_lit_type_Numeral x1)))) :named sm.axiom.$eo_lit_type_Numeral))

; program: $eo_lit_type_Rational
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_lit_type_Rational x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    eo.Real
    eo.Stuck))) :pattern (($eo_lit_type_Rational x1)))) :named sm.axiom.$eo_lit_type_Rational))

; program: $eo_lit_type_Binary
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_lit_type_Binary x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_mk_apply eo.BitVec ($eo_len x1))
    eo.Stuck))) :pattern (($eo_lit_type_Binary x1)))) :named sm.axiom.$eo_lit_type_Binary))

; program: $eo_lit_type_String
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_lit_type_String x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (eo.Apply eo.Seq eo.Char)
    eo.Stuck))) :pattern (($eo_lit_type_String x1)))) :named sm.axiom.$eo_lit_type_String))

; program: $eo_dt_selectors
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_dt_selectors x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
    eo.Stuck)) :pattern (($eo_dt_selectors x1)))) :named sm.axiom.$eo_dt_selectors))

; fwd-decl: $eo_model_sat
(declare-fun $eo_model_sat (eo.Term) eo.Term)

; fwd-decl: $eo_model_unsat
(declare-fun $eo_model_unsat (eo.Term) eo.Term)

; fwd-decl: $smtx_value_hash
(declare-fun $smtx_value_hash (vsm.Value) Int)

; fwd-decl: $smtx_reverse_value_hash
(declare-fun $smtx_reverse_value_hash (Int) vsm.Value)

; program: $smtx_msm_lookup
(declare-fun $smtx_msm_lookup (msm.Map vsm.Value) vsm.Value)
(assert (! (forall ((x1 msm.Map) (x2 vsm.Value))
  (! (= ($smtx_msm_lookup x1 x2)
  (ite (and ((_ is msm.cons) x1) (= x2 (msm.cons.arg1 x1)))
    (msm.cons.arg2 x1)
  (ite ((_ is msm.cons) x1)
    ($smtx_msm_lookup (msm.cons.arg3 x1) x2)
    (msm.default.arg1 x1)
))) :pattern (($smtx_msm_lookup x1 x2)))) :named sm.axiom.$smtx_msm_lookup))

; program: $smtx_is_atomic_term_value
(define-fun $smtx_is_atomic_term_value ((x1 eo.Term)) Bool
  (ite ((_ is eo.Boolean) x1)
    true
  (ite ((_ is eo.Numeral) x1)
    true
  (ite ((_ is eo.Rational) x1)
    true
  (ite ((_ is eo.String) x1)
    true
  (ite ((_ is eo.Binary) x1)
    (and (<= 0 (eo.Binary.arg1 x1)) (= (eo.Binary (eo.Binary.arg1 x1) (eo.Binary.arg2 x1)) (eo.Binary (eo.Binary.arg1 x1) (mod (eo.Binary.arg2 x1) ($smtx_pow2 (eo.Binary.arg1 x1))))))
    false
))))))

; fwd-decl: $smtx_model_eval
(declare-fun $smtx_model_eval (eo.Term) vsm.Value)

; program: $smtx_model_eval_apply
(define-fun $smtx_model_eval_apply ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Apply) x1)
    (vsm.Apply (vsm.Apply (vsm.Apply.arg1 x1) (vsm.Apply.arg2 x1)) x2)
  (ite ((_ is vsm.Map) x1)
    ($smtx_msm_lookup (vsm.Map.arg1 x1) x2)
    vsm.NotValue
)))

; program: $smtx_model_eval_=
(define-fun $smtx_model_eval_= ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Boolean) (vsm.Term.arg1 x1)) ((_ is vsm.Term) x2) ((_ is eo.Boolean) (vsm.Term.arg1 x2)))
    (vsm.Term (eo.Boolean (= (eo.Boolean (eo.Boolean.arg1 (vsm.Term.arg1 x1))) (eo.Boolean (eo.Boolean.arg1 (vsm.Term.arg1 x2))))))
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Boolean) (vsm.Term.arg1 x1)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x2) ((_ is eo.Boolean) (vsm.Term.arg1 x2)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Numeral) (vsm.Term.arg1 x1)) ((_ is vsm.Term) x2) ((_ is eo.Numeral) (vsm.Term.arg1 x2)))
    (vsm.Term (eo.Boolean (= (eo.Numeral (eo.Numeral.arg1 (vsm.Term.arg1 x1))) (eo.Numeral (eo.Numeral.arg1 (vsm.Term.arg1 x2))))))
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Numeral) (vsm.Term.arg1 x1)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x2) ((_ is eo.Numeral) (vsm.Term.arg1 x2)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Rational) (vsm.Term.arg1 x1)) ((_ is vsm.Term) x2) ((_ is eo.Rational) (vsm.Term.arg1 x2)))
    (vsm.Term (eo.Boolean (= (eo.Rational (eo.Rational.arg1 (vsm.Term.arg1 x1))) (eo.Rational (eo.Rational.arg1 (vsm.Term.arg1 x2))))))
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Rational) (vsm.Term.arg1 x1)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x2) ((_ is eo.Rational) (vsm.Term.arg1 x2)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.String) (vsm.Term.arg1 x1)) ((_ is vsm.Term) x2) ((_ is eo.String) (vsm.Term.arg1 x2)))
    (vsm.Term (eo.Boolean (= (eo.String (eo.String.arg1 (vsm.Term.arg1 x1))) (eo.String (eo.String.arg1 (vsm.Term.arg1 x2))))))
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.String) (vsm.Term.arg1 x1)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x2) ((_ is eo.String) (vsm.Term.arg1 x2)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Binary) (vsm.Term.arg1 x1)) ((_ is vsm.Term) x2) ((_ is eo.Binary) (vsm.Term.arg1 x2)))
    (ite (zeq (eo.Binary.arg1 (vsm.Term.arg1 x1)) (eo.Binary.arg1 (vsm.Term.arg1 x2))) (vsm.Term (eo.Boolean (= (eo.Binary (eo.Binary.arg1 (vsm.Term.arg1 x1)) (eo.Binary.arg2 (vsm.Term.arg1 x1))) (eo.Binary (eo.Binary.arg1 (vsm.Term.arg1 x2)) (eo.Binary.arg2 (vsm.Term.arg1 x2)))))) vsm.NotValue)
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Binary) (vsm.Term.arg1 x1)))
    vsm.NotValue
  (ite (and ((_ is vsm.Term) x2) ((_ is eo.Binary) (vsm.Term.arg1 x2)))
    vsm.NotValue
  (ite (= x1 vsm.NotValue)
    vsm.NotValue
  (ite (= x2 vsm.NotValue)
    vsm.NotValue
    (vsm.Term (eo.Boolean (= x1 x2)))
))))))))))))))))))

; program: $smtx_model_eval_not
(define-fun $smtx_model_eval_not ((x1 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Boolean) (vsm.Term.arg1 x1)))
    (vsm.Term (eo.Boolean (not (eo.Boolean.arg1 (vsm.Term.arg1 x1)))))
    vsm.NotValue
))

; program: $smtx_model_eval_and
(define-fun $smtx_model_eval_and ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Term) x1) ((_ is eo.Boolean) (vsm.Term.arg1 x1)) ((_ is vsm.Term) x2) ((_ is eo.Boolean) (vsm.Term.arg1 x2)))
    (vsm.Term (eo.Boolean (and (eo.Boolean.arg1 (vsm.Term.arg1 x1)) (eo.Boolean.arg1 (vsm.Term.arg1 x2)))))
    vsm.NotValue
))

; program: $smtx_model_eval
(assert (! (forall ((x1 eo.Term))
  (! (= ($smtx_model_eval x1)
  (ite (and ((_ is eo.Apply) x1) (= (eo.Apply.arg1 x1) eo.not))
    ($smtx_model_eval_not ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) (= (eo.Apply.arg1 (eo.Apply.arg1 x1)) eo.and))
    ($smtx_model_eval_and ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) (= (eo.Apply.arg1 (eo.Apply.arg1 x1)) eo.=))
    ($smtx_model_eval_= ($smtx_model_eval (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_model_eval (eo.Apply.arg2 x1)))
  (ite ((_ is eo.Apply) x1)
    ($smtx_model_eval_apply ($smtx_model_eval (eo.Apply.arg1 x1)) ($smtx_model_eval (eo.Apply.arg2 x1)))
    (ite ($smtx_is_atomic_term_value x1) (vsm.Term x1) (ite (not (= ($eo_dt_selectors x1) eo.Stuck)) (vsm.Apply (vsm.Term x1) vsm.NotValue) vsm.NotValue))
))))) :pattern (($smtx_model_eval x1)))) :named sm.axiom.$smtx_model_eval))

; program: $eo_model_sat
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_model_sat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (ite (= ($smtx_model_eval x1) (vsm.Term (eo.Boolean true))) (eo.Boolean true) (eo.Boolean false))
    eo.Stuck))) :pattern (($eo_model_sat x1)))) :named sm.axiom.$eo_model_sat))

; program: $eo_model_unsat
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_model_unsat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (ite (= ($smtx_model_eval x1) (vsm.Term (eo.Boolean false))) (eo.Boolean true) (eo.Boolean false))
    eo.Stuck))) :pattern (($eo_model_unsat x1)))) :named sm.axiom.$eo_model_unsat))

; program: $eovc_symm
(define-fun $eovc_symm ((x1 eo.Term)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_requires ($eo_typeof x1) eo.Bool ($eo_requires ($eo_model_sat x1) (eo.Boolean true) ($eo_requires ($eo_typeof ($eo_prog_symm (eo.$eo_pf x1))) eo.Bool ($eo_requires ($eo_model_unsat ($eo_prog_symm (eo.$eo_pf x1))) (eo.Boolean true) (eo.Boolean true)))))
    eo.Stuck)))



;;; Meta-level properties of models

; axiom for hash
; note: this implies that $smtx_hash is injective, which implies $eo_hash is injective.
(assert (! (forall ((x eo.Term))
    (! (= ($eo_reverse_hash ($smtx_hash x)) x) :pattern (($smtx_hash x)))) :named eo.hash_injective))
(assert (! (forall ((x vsm.Value))
    (! (= ($smtx_reverse_value_hash ($smtx_value_hash x)) x) :pattern (($smtx_value_hash x)))) :named smtx.hash_injective))


;;; The verification condition

;;;; final verification condition for $eovc_symm
(assert (! (exists ((x1 eo.Term))
  (= ($eovc_symm x1) (eo.Boolean true))) :named sm.conjecture.$eovc_symm))
(check-sat)

