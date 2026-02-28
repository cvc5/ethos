(set-logic ALL)

(define-sort Rat () Real)
(define-fun iff ((x Bool) (y Bool)) Bool (= x y))
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
(define-fun streq ((x String) (y String)) Bool (= x y))
(define-fun /_by_zero ((x Real)) Real (/ x 0.0))
(define-fun div_by_zero ((x Int)) Int (div x 0))
(define-fun mod_by_zero ((x Int)) Int (mod x 0))

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
(declare-datatypes
  ((eo.Term 0) (vsm.Value 0) (msm.Map 0) (ssm.Seq 0) (sm.Term 0) (tsm.Type 0) (dt.Datatype 0) (dtc.DatatypeCons 0))
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
  ; smt-cons: Datatype
  (eo.Datatype (eo.Datatype.arg1 String) (eo.Datatype.arg2 dt.Datatype))
  ; smt-cons: DtCons
  (eo.DtCons (eo.DtCons.arg1 String) (eo.DtCons.arg2 dt.Datatype) (eo.DtCons.arg3 Int))
  ; smt-cons: DtSel
  (eo.DtSel (eo.DtSel.arg1 String) (eo.DtSel.arg2 dt.Datatype) (eo.DtSel.arg3 Int) (eo.DtSel.arg4 Int))
  ; user-decl: not
  (eo.not)
  ; user-decl: and
  (eo.and)
  ; user-decl: =
  (eo.=)

  )
  (
  ; smt-cons: NotValue
  (vsm.NotValue)
  ; smt-cons: Boolean
  (vsm.Boolean (vsm.Boolean.arg1 Bool))
  ; smt-cons: Numeral
  (vsm.Numeral (vsm.Numeral.arg1 Int))
  ; smt-cons: Rational
  (vsm.Rational (vsm.Rational.arg1 Rat))
  ; smt-cons: String
  (vsm.String (vsm.String.arg1 String))
  ; smt-cons: Binary
  (vsm.Binary (vsm.Binary.arg1 Int) (vsm.Binary.arg2 Int))
  ; smt-cons: Map
  (vsm.Map (vsm.Map.arg1 msm.Map))
  ; smt-cons: Seq
  (vsm.Seq (vsm.Seq.arg1 ssm.Seq))
  ; smt-cons: RegLan
  (vsm.RegLan (vsm.RegLan.arg1 RegLan))
  ; smt-cons: Lambda
  (vsm.Lambda (vsm.Lambda.arg1 String) (vsm.Lambda.arg2 tsm.Type) (vsm.Lambda.arg3 sm.Term))
  ; smt-cons: DtCons
  (vsm.DtCons (vsm.DtCons.arg1 String) (vsm.DtCons.arg2 dt.Datatype) (vsm.DtCons.arg3 Int))
  ; smt-cons: Apply
  (vsm.Apply (vsm.Apply.arg1 vsm.Value) (vsm.Apply.arg2 vsm.Value))

  )
  (
  ; smt-cons: cons
  (msm.cons (msm.cons.arg1 vsm.Value) (msm.cons.arg2 vsm.Value) (msm.cons.arg3 msm.Map))
  ; smt-cons: default
  (msm.default (msm.default.arg1 tsm.Type) (msm.default.arg2 vsm.Value))

  )
  (
  ; smt-cons: cons
  (ssm.cons (ssm.cons.arg1 vsm.Value) (ssm.cons.arg2 ssm.Seq))
  ; smt-cons: empty
  (ssm.empty (ssm.empty.arg1 tsm.Type))

  )
  (
  ; smt-cons: None
  (sm.None)
  ; smt-cons: Boolean
  (sm.Boolean (sm.Boolean.arg1 Bool))
  ; smt-cons: Numeral
  (sm.Numeral (sm.Numeral.arg1 Int))
  ; smt-cons: Rational
  (sm.Rational (sm.Rational.arg1 Rat))
  ; smt-cons: String
  (sm.String (sm.String.arg1 String))
  ; smt-cons: Binary
  (sm.Binary (sm.Binary.arg1 Int) (sm.Binary.arg2 Int))
  ; smt-cons: Apply
  (sm.Apply (sm.Apply.arg1 sm.Term) (sm.Apply.arg2 sm.Term))
  ; smt-cons: Var
  (sm.Var (sm.Var.arg1 String) (sm.Var.arg2 tsm.Type))
  ; smt-cons: exists
  (sm.exists (sm.exists.arg1 String) (sm.exists.arg2 tsm.Type))
  ; smt-cons: forall
  (sm.forall (sm.forall.arg1 String) (sm.forall.arg2 tsm.Type))
  ; smt-cons: lambda
  (sm.lambda (sm.lambda.arg1 String) (sm.lambda.arg2 tsm.Type))
  ; smt-cons: choice
  (sm.choice (sm.choice.arg1 String) (sm.choice.arg2 tsm.Type))
  ; smt-cons: DtCons
  (sm.DtCons (sm.DtCons.arg1 String) (sm.DtCons.arg2 dt.Datatype) (sm.DtCons.arg3 Int))
  ; smt-cons: DtSel
  (sm.DtSel (sm.DtSel.arg1 String) (sm.DtSel.arg2 dt.Datatype) (sm.DtSel.arg3 Int) (sm.DtSel.arg4 Int))
  ; smt-cons: DtTester
  (sm.DtTester (sm.DtTester.arg1 String) (sm.DtTester.arg2 dt.Datatype) (sm.DtTester.arg3 Int))
  ; smt-cons: DtUpdater
  (sm.DtUpdater (sm.DtUpdater.arg1 String) (sm.DtUpdater.arg2 dt.Datatype) (sm.DtUpdater.arg3 Int) (sm.DtUpdater.arg4 Int))
  ; smt-cons: Const
  (sm.Const (sm.Const.arg1 vsm.Value) (sm.Const.arg2 tsm.Type))
  ; smt-cons: not
  (sm.not)
  ; smt-cons: and
  (sm.and)
  ; smt-cons: =
  (sm.=)

  )
  (
  ; smt-cons: None
  (tsm.None)
  ; smt-cons: Bool
  (tsm.Bool)
  ; smt-cons: Int
  (tsm.Int)
  ; smt-cons: Real
  (tsm.Real)
  ; smt-cons: String
  (tsm.String)
  ; smt-cons: RegLan
  (tsm.RegLan)
  ; smt-cons: BitVec
  (tsm.BitVec (tsm.BitVec.arg1 Int))
  ; smt-cons: Map
  (tsm.Map (tsm.Map.arg1 tsm.Type) (tsm.Map.arg2 tsm.Type))
  ; smt-cons: DtConsType
  (tsm.DtConsType (tsm.DtConsType.arg1 tsm.Type) (tsm.DtConsType.arg2 tsm.Type))
  ; smt-cons: Seq
  (tsm.Seq (tsm.Seq.arg1 tsm.Type))
  ; smt-cons: Datatype
  (tsm.Datatype (tsm.Datatype.arg1 String) (tsm.Datatype.arg2 dt.Datatype))
  ; smt-cons: TypeRef
  (tsm.TypeRef (tsm.TypeRef.arg1 String))
  ; smt-cons: Char
  (tsm.Char)

  )
  (
  (dt.null)
  (dt.sum (dt.sum.arg1 dtc.DatatypeCons) (dt.sum.arg2 dt.Datatype))
  )
  (
  (dtc.unit)
  (dtc.cons (dtc.cons.arg1 tsm.Type) (dtc.cons.arg2 dtc.DatatypeCons))
  )
  )
)

(define-fun teq ((x eo.Term) (y eo.Term)) Bool (= x y))
(define-fun Teq ((x tsm.Type) (y tsm.Type)) Bool (= x y))
(define-fun veq ((x vsm.Value) (y vsm.Value)) Bool (= x y))

; forward declarations
(declare-fun texists (String tsm.Type sm.Term) vsm.Value)
(declare-fun tforall (String tsm.Type sm.Term) vsm.Value)
(declare-fun tchoice (String tsm.Type sm.Term) vsm.Value)
(declare-fun tlambda (String tsm.Type sm.Term) vsm.Value)
  
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

; program: $smtx_pow2
(define-fun $smtx_pow2 ((x1 Int)) Int
    (int.pow2 x1)
)

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

; program: $eo_Datatype
(define-fun $eo_Datatype ((x1 String) (x2 dt.Datatype)) eo.Term
    (eo.Datatype x1 x2)
)

; program: $eo_DtCons
(define-fun $eo_DtCons ((x1 String) (x2 dt.Datatype) (x3 Int)) eo.Term
    (eo.DtCons x1 x2 x3)
)

; program: $eo_DtSel
(define-fun $eo_DtSel ((x1 String) (x2 dt.Datatype) (x3 Int) (x4 Int)) eo.Term
    (eo.DtSel x1 x2 x3 x4)
)

; program: $eo_mk_apply
(define-fun $eo_mk_apply ((x1 eo.Term) (x2 eo.Term)) eo.Term
  (ite (or (= x1 eo.Stuck) (= x2 eo.Stuck))
    eo.Stuck
  (ite true
    (eo.Apply x1 x2)
    eo.Stuck)))

; program: $eo_requires
(define-fun $eo_requires ((x1 eo.Term) (x2 eo.Term) (x3 eo.Term)) eo.Term
    (ite (teq x1 x2) (ite (not (teq x1 eo.Stuck)) x3 eo.Stuck) eo.Stuck)
)

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
  (ite ((_ is eo.Datatype) x1)
    eo.Type
  (ite true
    ($eo_typeof_main x1)
    eo.Stuck)))))))))) :pattern (($eo_typeof x1)))) :named sm.axiom.$eo_typeof))

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

; fwd-decl: $eo_model_sat
(declare-fun $eo_model_sat (eo.Term) eo.Term)

; fwd-decl: $eo_model_unsat
(declare-fun $eo_model_unsat (eo.Term) eo.Term)

; program: $vsm_apply_head
(declare-fun $vsm_apply_head (vsm.Value) vsm.Value)
(assert (! (forall ((x1 vsm.Value))
  (! (= ($vsm_apply_head x1)
  (ite ((_ is vsm.Apply) x1)
    ($vsm_apply_head (vsm.Apply.arg1 x1))
    x1
)) :pattern (($vsm_apply_head x1)))) :named sm.axiom.$vsm_apply_head))

; program: $vsm_apply_arg_nth
(declare-fun $vsm_apply_arg_nth (vsm.Value Int) vsm.Value)
(assert (! (forall ((x1 vsm.Value) (x2 Int))
  (! (= ($vsm_apply_arg_nth x1 x2)
  (ite ((_ is vsm.Apply) x1)
    (ite (zeq x2 0) (vsm.Apply.arg2 x1) ($vsm_apply_arg_nth (vsm.Apply.arg1 x1) (zplus x2 (zneg 1))))
    vsm.NotValue
)) :pattern (($vsm_apply_arg_nth x1 x2)))) :named sm.axiom.$vsm_apply_arg_nth))

; fwd-decl: $smtx_value_hash
(declare-fun $smtx_value_hash (vsm.Value) Int)

; fwd-decl: $smtx_reverse_value_hash
(declare-fun $smtx_reverse_value_hash (Int) vsm.Value)

; fwd-decl: $smtx_typeof_value
(declare-fun $smtx_typeof_value (vsm.Value) tsm.Type)

; program: $smtx_msm_lookup
(declare-fun $smtx_msm_lookup (msm.Map vsm.Value) vsm.Value)
(assert (! (forall ((x1 msm.Map) (x2 vsm.Value))
  (! (= ($smtx_msm_lookup x1 x2)
  (ite ((_ is msm.cons) x1)
    (ite (veq (msm.cons.arg1 x1) x2) (msm.cons.arg2 x1) ($smtx_msm_lookup (msm.cons.arg3 x1) x2))
    (msm.default.arg2 x1)
)) :pattern (($smtx_msm_lookup x1 x2)))) :named sm.axiom.$smtx_msm_lookup))

; program: $smtx_typeof_map_value
(declare-fun $smtx_typeof_map_value (msm.Map) tsm.Type)
(assert (! (forall ((x1 msm.Map))
  (! (= ($smtx_typeof_map_value x1)
  (ite ((_ is msm.cons) x1)
    (ite (Teq (tsm.Map ($smtx_typeof_value (msm.cons.arg1 x1)) ($smtx_typeof_value (msm.cons.arg2 x1))) ($smtx_typeof_map_value (msm.cons.arg3 x1))) ($smtx_typeof_map_value (msm.cons.arg3 x1)) tsm.None)
    (tsm.Map (msm.default.arg1 x1) ($smtx_typeof_value (msm.default.arg2 x1)))
)) :pattern (($smtx_typeof_map_value x1)))) :named sm.axiom.$smtx_typeof_map_value))

; program: $smtx_typeof_seq_value
(declare-fun $smtx_typeof_seq_value (ssm.Seq) tsm.Type)
(assert (! (forall ((x1 ssm.Seq))
  (! (= ($smtx_typeof_seq_value x1)
  (ite ((_ is ssm.cons) x1)
    (ite (Teq (tsm.Seq ($smtx_typeof_value (ssm.cons.arg1 x1))) ($smtx_typeof_seq_value (ssm.cons.arg2 x1))) ($smtx_typeof_seq_value (ssm.cons.arg2 x1)) tsm.None)
    (tsm.Seq (ssm.empty.arg1 x1))
)) :pattern (($smtx_typeof_seq_value x1)))) :named sm.axiom.$smtx_typeof_seq_value))

; program: $smtx_dtc_substitute
(declare-fun $smtx_dtc_substitute (String dt.Datatype dtc.DatatypeCons) dtc.DatatypeCons)
(assert (! (forall ((x1 String) (x2 dt.Datatype) (x3 dtc.DatatypeCons))
  (! (= ($smtx_dtc_substitute x1 x2 x3)
  (ite ((_ is dtc.cons) x3)
    (dtc.cons (ite (Teq (dtc.cons.arg1 x3) (tsm.TypeRef x1)) (tsm.Datatype x1 x2) (dtc.cons.arg1 x3)) ($smtx_dtc_substitute x1 x2 (dtc.cons.arg2 x3)))
    dtc.unit
)) :pattern (($smtx_dtc_substitute x1 x2 x3)))) :named sm.axiom.$smtx_dtc_substitute))

; program: $smtx_dt_substitute
(declare-fun $smtx_dt_substitute (String dt.Datatype dt.Datatype) dt.Datatype)
(assert (! (forall ((x1 String) (x2 dt.Datatype) (x3 dt.Datatype))
  (! (= ($smtx_dt_substitute x1 x2 x3)
  (ite ((_ is dt.sum) x3)
    (dt.sum ($smtx_dtc_substitute x1 x2 (dt.sum.arg1 x3)) ($smtx_dt_substitute x1 x2 (dt.sum.arg2 x3)))
    dt.null
)) :pattern (($smtx_dt_substitute x1 x2 x3)))) :named sm.axiom.$smtx_dt_substitute))

; program: $smtx_typeof_dt_cons_value_rec
(declare-fun $smtx_typeof_dt_cons_value_rec (tsm.Type dt.Datatype Int) tsm.Type)
(assert (! (forall ((x1 tsm.Type) (x2 dt.Datatype) (x3 Int))
  (! (= ($smtx_typeof_dt_cons_value_rec x1 x2 x3)
  (ite (and (= x2 dt.null) (= x3 0))
    x1
  (ite (and ((_ is dt.sum) x2) ((_ is dtc.cons) (dt.sum.arg1 x2)) (= x3 0))
    (tsm.DtConsType (dtc.cons.arg1 (dt.sum.arg1 x2)) ($smtx_typeof_dt_cons_value_rec x1 (dt.sum (dtc.cons.arg2 (dt.sum.arg1 x2)) (dt.sum.arg2 x2)) 0))
  (ite ((_ is dt.sum) x2)
    ($smtx_typeof_dt_cons_value_rec x1 (dt.sum.arg2 x2) (zplus x3 (zneg 1)))
    tsm.None
)))) :pattern (($smtx_typeof_dt_cons_value_rec x1 x2 x3)))) :named sm.axiom.$smtx_typeof_dt_cons_value_rec))

; program: $smtx_typeof_apply_value
(define-fun $smtx_typeof_apply_value ((x1 tsm.Type) (x2 tsm.Type)) tsm.Type
  (ite ((_ is tsm.DtConsType) x1)
    (ite (Teq (tsm.DtConsType.arg1 x1) x2) (tsm.DtConsType.arg2 x1) tsm.None)
    tsm.None
))

; program: $smtx_typeof_value
(assert (! (forall ((x1 vsm.Value))
  (! (= ($smtx_typeof_value x1)
  (ite ((_ is vsm.Boolean) x1)
    tsm.Bool
  (ite ((_ is vsm.Numeral) x1)
    tsm.Int
  (ite ((_ is vsm.Rational) x1)
    tsm.Real
  (ite ((_ is vsm.String) x1)
    tsm.String
  (ite ((_ is vsm.Binary) x1)
    (ite (zleq 0 (vsm.Binary.arg1 x1)) (tsm.BitVec (vsm.Binary.arg1 x1)) tsm.None)
  (ite ((_ is vsm.RegLan) x1)
    tsm.RegLan
  (ite ((_ is vsm.Map) x1)
    ($smtx_typeof_map_value (vsm.Map.arg1 x1))
  (ite ((_ is vsm.Seq) x1)
    ($smtx_typeof_seq_value (vsm.Seq.arg1 x1))
  (ite ((_ is vsm.DtCons) x1)
    ($smtx_typeof_dt_cons_value_rec (tsm.Datatype (vsm.DtCons.arg1 x1) (vsm.DtCons.arg2 x1)) ($smtx_dt_substitute (vsm.DtCons.arg1 x1) (vsm.DtCons.arg2 x1) (vsm.DtCons.arg2 x1)) (vsm.DtCons.arg3 x1))
  (ite ((_ is vsm.Apply) x1)
    ($smtx_typeof_apply_value ($smtx_typeof_value (vsm.Apply.arg1 x1)) ($smtx_typeof_value (vsm.Apply.arg2 x1)))
    tsm.None
))))))))))) :pattern (($smtx_typeof_value x1)))) :named sm.axiom.$smtx_typeof_value))

; fwd-decl: $smtx_model_eval
(declare-fun $smtx_model_eval (sm.Term) vsm.Value)

; program: $smtx_model_eval_=
(define-fun $smtx_model_eval_= ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
    (ite (Teq ($smtx_typeof_value x1) ($smtx_typeof_value x2)) (ite (Teq ($smtx_typeof_value x1) tsm.None) vsm.NotValue (vsm.Boolean (veq x1 x2))) vsm.NotValue)
)

; program: $smtx_is_var
(define-fun $smtx_is_var ((x1 String) (x2 tsm.Type) (x3 sm.Term)) Bool
  (ite ((_ is sm.Var) x3)
    (and (streq x1 (sm.Var.arg1 x3)) (Teq x2 (sm.Var.arg2 x3)))
    false
))

; program: $smtx_is_binder_x
(define-fun $smtx_is_binder_x ((x1 String) (x2 tsm.Type) (x3 sm.Term)) Bool
  (ite ((_ is sm.exists) x3)
    ($smtx_is_var x1 x2 (sm.Var (sm.exists.arg1 x3) (sm.exists.arg2 x3)))
  (ite ((_ is sm.forall) x3)
    ($smtx_is_var x1 x2 (sm.Var (sm.forall.arg1 x3) (sm.forall.arg2 x3)))
  (ite ((_ is sm.lambda) x3)
    ($smtx_is_var x1 x2 (sm.Var (sm.lambda.arg1 x3) (sm.lambda.arg2 x3)))
  (ite ((_ is sm.choice) x3)
    ($smtx_is_var x1 x2 (sm.Var (sm.choice.arg1 x3) (sm.choice.arg2 x3)))
    false
)))))

; program: $smtx_substitute
(declare-fun $smtx_substitute (String tsm.Type sm.Term sm.Term) sm.Term)
(assert (! (forall ((x1 String) (x2 tsm.Type) (x3 sm.Term) (x4 sm.Term))
  (! (= ($smtx_substitute x1 x2 x3 x4)
  (ite ((_ is sm.Apply) x4)
    (ite ($smtx_is_binder_x x1 x2 (sm.Apply.arg1 x4)) (sm.Apply (sm.Apply.arg1 x4) (sm.Apply.arg2 x4)) (sm.Apply ($smtx_substitute x1 x2 x3 (sm.Apply.arg1 x4)) ($smtx_substitute x1 x2 x3 (sm.Apply.arg2 x4))))
    (ite ($smtx_is_var x1 x2 x4) x3 x4)
)) :pattern (($smtx_substitute x1 x2 x3 x4)))) :named sm.axiom.$smtx_substitute))

; program: $smtx_model_eval_dt_cons
(define-fun $smtx_model_eval_dt_cons ((x1 String) (x2 dt.Datatype) (x3 Int)) vsm.Value
    (ite (Teq ($smtx_typeof_dt_cons_value_rec (tsm.Datatype x1 x2) ($smtx_dt_substitute x1 x2 x2) x3) tsm.None) vsm.NotValue (vsm.DtCons x1 x2 x3))
)

; program: $smtx_model_eval_dt_sel
(define-fun $smtx_model_eval_dt_sel ((x1 String) (x2 dt.Datatype) (x3 Int) (x4 Int) (x5 vsm.Value)) vsm.Value
    (ite (Teq ($smtx_typeof_value x5) (tsm.Datatype x1 x2)) (ite (veq ($vsm_apply_head x5) (vsm.DtCons x1 x2 x3)) ($vsm_apply_arg_nth x5 x4) vsm.NotValue) vsm.NotValue)
)

; program: $smtx_model_eval_dt_tester
(define-fun $smtx_model_eval_dt_tester ((x1 String) (x2 dt.Datatype) (x3 Int) (x4 vsm.Value)) vsm.Value
    (ite (Teq ($smtx_typeof_value x4) (tsm.Datatype x1 x2)) (vsm.Boolean (veq ($vsm_apply_head x4) (vsm.DtCons x1 x2 x3))) vsm.NotValue)
)

; program: $smtx_model_eval_dt_updater
(define-fun $smtx_model_eval_dt_updater ((x1 String) (x2 dt.Datatype) (x3 Int) (x4 Int) (x5 vsm.Value) (x6 vsm.Value)) vsm.Value
    vsm.NotValue
)

; program: $smtx_model_eval_apply
(define-fun $smtx_model_eval_apply ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Apply) x1)
    (vsm.Apply (vsm.Apply (vsm.Apply.arg1 x1) (vsm.Apply.arg2 x1)) x2)
  (ite ((_ is vsm.Map) x1)
    ($smtx_msm_lookup (vsm.Map.arg1 x1) x2)
    vsm.NotValue
)))

; program: $smtx_model_eval_not
(define-fun $smtx_model_eval_not ((x1 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Boolean) x1)
    (vsm.Boolean (not (vsm.Boolean.arg1 x1)))
    vsm.NotValue
))

; program: $smtx_model_eval_and
(define-fun $smtx_model_eval_and ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Boolean) x1) ((_ is vsm.Boolean) x2))
    (vsm.Boolean (and (vsm.Boolean.arg1 x1) (vsm.Boolean.arg1 x2)))
    vsm.NotValue
))

; program: $smtx_model_eval
(assert (! (forall ((x1 sm.Term))
  (! (= ($smtx_model_eval x1)
  (ite ((_ is sm.Boolean) x1)
    (vsm.Boolean (sm.Boolean.arg1 x1))
  (ite ((_ is sm.Numeral) x1)
    (vsm.Numeral (sm.Numeral.arg1 x1))
  (ite ((_ is sm.Rational) x1)
    (vsm.Rational (sm.Rational.arg1 x1))
  (ite ((_ is sm.String) x1)
    (vsm.String (sm.String.arg1 x1))
  (ite ((_ is sm.Binary) x1)
    (ite (and (zleq 0 (sm.Binary.arg1 x1)) (zeq (sm.Binary.arg2 x1) (mod (sm.Binary.arg2 x1) ($smtx_pow2 (sm.Binary.arg1 x1))))) (vsm.Binary (sm.Binary.arg1 x1) (sm.Binary.arg2 x1)) vsm.NotValue)
  (ite (and ((_ is sm.Apply) x1) (= (sm.Apply.arg1 x1) sm.not))
    ($smtx_model_eval_not ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) (= (sm.Apply.arg1 (sm.Apply.arg1 x1)) sm.and))
    ($smtx_model_eval_and ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) (= (sm.Apply.arg1 (sm.Apply.arg1 x1)) sm.=))
    ($smtx_model_eval_= ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.exists) (sm.Apply.arg1 x1)))
    (tforall (sm.exists.arg1 (sm.Apply.arg1 x1)) (sm.exists.arg2 (sm.Apply.arg1 x1)) (sm.Apply.arg2 x1))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.forall) (sm.Apply.arg1 x1)))
    (texists (sm.forall.arg1 (sm.Apply.arg1 x1)) (sm.forall.arg2 (sm.Apply.arg1 x1)) (sm.Apply.arg2 x1))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.lambda) (sm.Apply.arg1 x1)))
    (vsm.Lambda (sm.lambda.arg1 (sm.Apply.arg1 x1)) (sm.lambda.arg2 (sm.Apply.arg1 x1)) (sm.Apply.arg2 x1))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.choice) (sm.Apply.arg1 x1)))
    (tchoice (sm.choice.arg1 (sm.Apply.arg1 x1)) (sm.choice.arg2 (sm.Apply.arg1 x1)) (sm.Apply.arg2 x1))
  (ite ((_ is sm.DtCons) x1)
    ($smtx_model_eval_dt_cons (sm.DtCons.arg1 x1) (sm.DtCons.arg2 x1) (sm.DtCons.arg3 x1))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.DtSel) (sm.Apply.arg1 x1)))
    ($smtx_model_eval_dt_sel (sm.DtSel.arg1 (sm.Apply.arg1 x1)) (sm.DtSel.arg2 (sm.Apply.arg1 x1)) (sm.DtSel.arg3 (sm.Apply.arg1 x1)) (sm.DtSel.arg4 (sm.Apply.arg1 x1)) ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.DtTester) (sm.Apply.arg1 x1)))
    ($smtx_model_eval_dt_tester (sm.DtTester.arg1 (sm.Apply.arg1 x1)) (sm.DtTester.arg2 (sm.Apply.arg1 x1)) (sm.DtTester.arg3 (sm.Apply.arg1 x1)) ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) ((_ is sm.DtUpdater) (sm.Apply.arg1 (sm.Apply.arg1 x1))))
    ($smtx_model_eval_dt_updater (sm.DtUpdater.arg1 (sm.Apply.arg1 (sm.Apply.arg1 x1))) (sm.DtUpdater.arg2 (sm.Apply.arg1 (sm.Apply.arg1 x1))) (sm.DtUpdater.arg3 (sm.Apply.arg1 (sm.Apply.arg1 x1))) (sm.DtUpdater.arg4 (sm.Apply.arg1 (sm.Apply.arg1 x1))) ($smtx_model_eval (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite ((_ is sm.Apply) x1)
    ($smtx_model_eval_apply ($smtx_model_eval (sm.Apply.arg1 x1)) ($smtx_model_eval (sm.Apply.arg2 x1)))
  (ite ((_ is sm.Const) x1)
    (ite (Teq ($smtx_typeof_value (sm.Const.arg1 x1)) (sm.Const.arg2 x1)) (sm.Const.arg1 x1) vsm.NotValue)
    vsm.NotValue
))))))))))))))))))) :pattern (($smtx_model_eval x1)))) :named sm.axiom.$smtx_model_eval))

; program: $eo_to_smt_type
(declare-fun $eo_to_smt_type (eo.Term) tsm.Type)
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_to_smt_type x1)
  (ite (= x1 eo.Bool)
    tsm.Bool
  (ite ((_ is eo.Datatype) x1)
    (tsm.Datatype (eo.Datatype.arg1 x1) (eo.Datatype.arg2 x1))
  (ite (= x1 eo.Int)
    tsm.Int
  (ite (= x1 eo.Real)
    tsm.Real
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Numeral) (eo.Apply.arg2 x1)) (= (eo.Apply.arg1 x1) eo.BitVec))
    (tsm.BitVec (eo.Numeral.arg1 (eo.Apply.arg2 x1)))
  (ite (= x1 eo.Char)
    tsm.Char
  (ite (and ((_ is eo.Apply) x1) (= (eo.Apply.arg1 x1) eo.Seq))
    (tsm.Seq ($eo_to_smt_type (eo.Apply.arg2 x1)))
    tsm.None
)))))))) :pattern (($eo_to_smt_type x1)))) :named sm.axiom.$eo_to_smt_type))

; program: $eo_to_smt
(declare-fun $eo_to_smt (eo.Term) sm.Term)
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_to_smt x1)
  (ite ((_ is eo.Boolean) x1)
    (sm.Boolean (eo.Boolean.arg1 x1))
  (ite ((_ is eo.Numeral) x1)
    (sm.Numeral (eo.Numeral.arg1 x1))
  (ite ((_ is eo.Rational) x1)
    (sm.Rational (eo.Rational.arg1 x1))
  (ite ((_ is eo.String) x1)
    (sm.String (eo.String.arg1 x1))
  (ite ((_ is eo.Binary) x1)
    (sm.Binary (eo.Binary.arg1 x1) (eo.Binary.arg2 x1))
  (ite ((_ is eo.Var) x1)
    (sm.Var (eo.Var.arg1 x1) ($eo_to_smt_type (eo.Var.arg2 x1)))
  (ite ((_ is eo.DtCons) x1)
    (sm.DtCons (eo.DtCons.arg1 x1) (eo.DtCons.arg2 x1) (eo.DtCons.arg3 x1))
  (ite ((_ is eo.DtSel) x1)
    (sm.DtSel (eo.DtSel.arg1 x1) (eo.DtSel.arg2 x1) (eo.DtSel.arg3 x1) (eo.DtSel.arg4 x1))
  (ite (and ((_ is eo.Apply) x1) (= (eo.Apply.arg1 x1) eo.not))
    (sm.Apply sm.not ($eo_to_smt (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) (= (eo.Apply.arg1 (eo.Apply.arg1 x1)) eo.and))
    (sm.Apply (sm.Apply sm.and ($eo_to_smt (eo.Apply.arg2 (eo.Apply.arg1 x1)))) ($eo_to_smt (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) (= (eo.Apply.arg1 (eo.Apply.arg1 x1)) eo.=))
    (sm.Apply (sm.Apply sm.= ($eo_to_smt (eo.Apply.arg2 (eo.Apply.arg1 x1)))) ($eo_to_smt (eo.Apply.arg2 x1)))
  (ite ((_ is eo.Apply) x1)
    (sm.Apply ($eo_to_smt (eo.Apply.arg1 x1)) ($eo_to_smt (eo.Apply.arg2 x1)))
    sm.None
))))))))))))) :pattern (($eo_to_smt x1)))) :named sm.axiom.$eo_to_smt))

; program: $eo_model_sat
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_model_sat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (ite (veq ($smtx_model_eval ($eo_to_smt x1)) (vsm.Boolean true)) (eo.Boolean true) (eo.Boolean false))
    eo.Stuck))) :pattern (($eo_model_sat x1)))) :named sm.axiom.$eo_model_sat))

; program: $eo_model_unsat
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_model_unsat x1)
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    (ite (veq ($smtx_model_eval ($eo_to_smt x1)) (vsm.Boolean false)) (eo.Boolean true) (eo.Boolean false))
    eo.Stuck))) :pattern (($eo_model_unsat x1)))) :named sm.axiom.$eo_model_unsat))

; program: $mk_vsm_bool
(define-fun $mk_vsm_bool ((x1 Bool)) vsm.Value
    (vsm.Boolean x1)
)

; program: $mk_sm_const
(define-fun $mk_sm_const ((x1 vsm.Value) (x2 tsm.Type)) sm.Term
    (sm.Const x1 x2)
)

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

; true iff there exists a value of type T that when substituted into F
; is evaluated as tgt. Note that we do not check the type of T here,
; instead $smtx_substitute will generate terms ($sm_Const v T), which
; only evaluate to v if it is of type T.
(define-fun texists_total ((s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (exists ((v vsm.Value))
    (= ($smtx_model_eval ($smtx_substitute s T ($mk_sm_const v T) F)) tgt)))

; true iff all values of type T when substituted into F are evaluated as tgt.
(define-fun tforall_total ((s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (forall ((v vsm.Value))
    (= ($smtx_model_eval ($smtx_substitute s T ($mk_sm_const v T) F)) tgt)))

; exists
(assert (forall ((s String) (T tsm.Type) (F sm.Term))
  (= (texists s T F)
     (ite (texists_total s T F ($mk_vsm_bool true)) ($mk_vsm_bool true)
     (ite (tforall_total s T F ($mk_vsm_bool false)) ($mk_vsm_bool false)
       vsm.NotValue)))))
  
; forall
(assert (forall ((s String) (T tsm.Type) (F sm.Term))
  (= (tforall s T F)
     (ite (texists_total s T F ($mk_vsm_bool false)) ($mk_vsm_bool false)
     (ite (tforall_total s T F ($mk_vsm_bool true)) ($mk_vsm_bool true)
       vsm.NotValue)))))

; choice
; If there exists a value making the existential true, we can assume
; that substituting with choice also makes it true.
(assert (forall ((s String) (T tsm.Type) (F sm.Term) (v vsm.Value))
  (=> (texists_total s T F ($mk_vsm_bool true))
      (= ($smtx_model_eval ($smtx_substitute s T ($mk_sm_const (tchoice s T F) T) F))
         ($mk_vsm_bool true)))))

;;; The verification condition

;;;; final verification condition for $eovc_symm
(assert (! (exists ((x1 eo.Term))
  (= ($eovc_symm x1) (eo.Boolean true))) :named sm.conjecture.$eovc_symm))
(check-sat)

