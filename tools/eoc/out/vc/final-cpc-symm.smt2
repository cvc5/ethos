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
(define-fun zdiv_total ((x Int) (y Int)) Real (/_total (to_real x) (to_real y)))
(define-fun qdiv_total ((x Real) (y Real)) Real (/_total x y))
(define-sort Char () Int)
(define-fun streq ((x String) (y String)) Bool (= x y))

(declare-datatype Nat ((nat.zero) (nat.succ (nat.succ.arg1 Nat))))
(define-fun nateq ((x Nat) (y Nat)) Bool (= x y))
(declare-fun int.to_nat (Int) Nat)
(assert (! (forall ((x Int)) 
  (! (= (int.to_nat x) (ite (<= x 0) nat.zero (nat.succ (int.to_nat (- x 1)))))
  :pattern ((int.to_nat x))))
  :named smtx.int.to_nat.def))
(declare-fun nat.to_int (Nat) Int)
(assert (! (forall ((x Nat)) 
  (! (= (nat.to_int x) (ite ((_ is nat.succ) x) (+ 1 (nat.to_int (nat.succ.arg1 x))) 0))
  :pattern ((nat.to_int x))))
  :named smtx.nat.to_int.def))
  
; uninterpreted constant identifier for builtin partial functions
(define-fun /_by_zero_id () String "@/_by_zero")
(define-fun div_by_zero_id () String "@div_by_zero")
(define-fun mod_by_zero_id () String "@mod_by_zero")
(define-fun wrong_apply_sel_id () String "@wrong_apply_sel")
(define-fun oob_seq_nth_id () String "@oob_seq_nth")
(define-fun uconst_id ((x Nat)) String (str.++ "@u." (str.from_int (nat.to_int x))))

; integer exponentiation is not handled by cvc5, axiomatize it
(declare-fun zexp_total (Int Int) Int)
(assert (! (forall ((x Int) (y Int)) 
  (! (= (zexp_total x y) (ite (< y 0) 0 (ite (= y 0) 1 (* x (zexp_total x (- y 1))))))
  :pattern ((zexp_total x y))))
  :named smtx.zexp_total.def))

(define-fun bit ((x1 Int) (x2 Int)) Bool
  (zeq 1 (mod (div x1 (int.pow2 x2)) 2)))
(define-fun msb ((x1 Int) (x2 Int)) Bool
  (bit x2 (zplus x1 (zneg 1))))
(define-fun binary_and ((x1 Int) (x2 Int) (x3 Int)) Int
  (ite (zeq x1 0) 0 (piand x1 x2 x3)))
(define-fun binary_or ((x1 Int) (x2 Int) (x3 Int)) Int
  (zplus x2 (zplus x3 (zneg (ite (zeq x1 0) 0 (piand x1 x2 x3))))))
(define-fun binary_xor ((x1 Int) (x2 Int) (x3 Int)) Int
  (zplus x2 (zplus x3 (zneg (zmult 2 (ite (zeq x1 0) 0 (piand x1 x2 x3)))))))
(define-fun binary_not ((x1 Int) (x2 Int)) Int
  (zplus (int.pow2 x1) (zneg (zplus x2 1))))
(define-fun binary_max ((x1 Int)) Int
  (zplus (int.pow2 x1) (zneg 1)))
(define-fun binary_uts ((w Int) (n Int)) Int
  (zplus (zmult 2 (mod n (int.pow2 (zplus w (zneg 1))))) (zneg n)))
(define-fun binary_concat ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int
  (zplus (zmult x2 (int.pow2 x3)) x4))
(define-fun binary_extract ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int
  (div x2 (int.pow2 x4)))
    
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
  ((eo.Term 0)  (edt.Datatype 0) (edtc.DatatypeCons 0)
   (vsm.Value 0) (msm.Map 0) (ssm.Seq 0) (sm.Term 0) (tsm.Type 0)
   (dt.Datatype 0) (dtc.DatatypeCons 0))
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
  ; smt-cons: DatatypeType
  (eo.DatatypeType (eo.DatatypeType.arg1 String) (eo.DatatypeType.arg2 edt.Datatype))
  ; smt-cons: DtCons
  (eo.DtCons (eo.DtCons.arg1 String) (eo.DtCons.arg2 edt.Datatype) (eo.DtCons.arg3 Nat))
  ; smt-cons: DtSel
  (eo.DtSel (eo.DtSel.arg1 String) (eo.DtSel.arg2 edt.Datatype) (eo.DtSel.arg3 Nat) (eo.DtSel.arg4 Nat))
  ; smt-cons: USort
  (eo.USort (eo.USort.arg1 Nat))
  ; smt-cons: UConst
  (eo.UConst (eo.UConst.arg1 Nat) (eo.UConst.arg2 eo.Term))
  ; user-decl: not
  (eo.not)
  ; user-decl: and
  (eo.and)
  ; user-decl: =
  (eo.=)

  )
  (
  (edt.null)
  (edt.sum (edt.sum.arg1 edtc.DatatypeCons) (edt.sum.arg2 edt.Datatype))
  )
  (
  (edtc.unit)
  (edtc.cons (edtc.cons.arg1 eo.Term) (edtc.cons.arg2 edtc.DatatypeCons))
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
  ; smt-cons: Binary
  (vsm.Binary (vsm.Binary.arg1 Int) (vsm.Binary.arg2 Int))
  ; smt-cons: Map
  (vsm.Map (vsm.Map.arg1 msm.Map))
  ; smt-cons: Set
  (vsm.Set (vsm.Set.arg1 msm.Map))
  ; smt-cons: Seq
  (vsm.Seq (vsm.Seq.arg1 ssm.Seq))
  ; smt-cons: Char
  (vsm.Char (vsm.Char.arg1 Char))
  ; smt-cons: RegLan
  (vsm.RegLan (vsm.RegLan.arg1 RegLan))
  ; smt-cons: DtCons
  (vsm.DtCons (vsm.DtCons.arg1 String) (vsm.DtCons.arg2 dt.Datatype) (vsm.DtCons.arg3 Nat))
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
  ; smt-cons: ite
  (sm.ite)
  ; smt-cons: =
  (sm.=)
  ; smt-cons: exists
  (sm.exists (sm.exists.arg1 String) (sm.exists.arg2 tsm.Type))
  ; smt-cons: forall
  (sm.forall (sm.forall.arg1 String) (sm.forall.arg2 tsm.Type))
  ; smt-cons: choice
  (sm.choice (sm.choice.arg1 String) (sm.choice.arg2 tsm.Type))
  ; smt-cons: DtCons
  (sm.DtCons (sm.DtCons.arg1 String) (sm.DtCons.arg2 dt.Datatype) (sm.DtCons.arg3 Nat))
  ; smt-cons: DtSel
  (sm.DtSel (sm.DtSel.arg1 String) (sm.DtSel.arg2 dt.Datatype) (sm.DtSel.arg3 Nat) (sm.DtSel.arg4 Nat))
  ; smt-cons: DtTester
  (sm.DtTester (sm.DtTester.arg1 String) (sm.DtTester.arg2 dt.Datatype) (sm.DtTester.arg3 Nat))
  ; smt-cons: UConst
  (sm.UConst (sm.UConst.arg1 String) (sm.UConst.arg2 tsm.Type))
  ; smt-cons: not
  (sm.not)
  ; smt-cons: and
  (sm.and)

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
  ; smt-cons: RegLan
  (tsm.RegLan)
  ; smt-cons: BitVec
  (tsm.BitVec (tsm.BitVec.arg1 Int))
  ; smt-cons: Map
  (tsm.Map (tsm.Map.arg1 tsm.Type) (tsm.Map.arg2 tsm.Type))
  ; smt-cons: Set
  (tsm.Set (tsm.Set.arg1 tsm.Type))
  ; smt-cons: Seq
  (tsm.Seq (tsm.Seq.arg1 tsm.Type))
  ; smt-cons: Char
  (tsm.Char)
  ; smt-cons: Datatype
  (tsm.Datatype (tsm.Datatype.arg1 String) (tsm.Datatype.arg2 dt.Datatype))
  ; smt-cons: TypeRef
  (tsm.TypeRef (tsm.TypeRef.arg1 String))
  ; smt-cons: USort
  (tsm.USort (tsm.USort.arg1 Nat))
  ; smt-cons: DtConsType
  (tsm.DtConsType (tsm.DtConsType.arg1 tsm.Type) (tsm.DtConsType.arg2 tsm.Type))

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

; sequences and string conversions
(declare-fun unpack_seq (ssm.Seq) (Seq vsm.Value))
(declare-fun pack_seq (tsm.Type (Seq vsm.Value)) ssm.Seq)
(declare-fun unpack_string (ssm.Seq) String)
(declare-fun pack_string (String) ssm.Seq)
(declare-fun char_of_value (vsm.Value) String)

(assert (! (forall ((x ssm.Seq))
  (! (= (unpack_seq x) 
    (ite ((_ is ssm.cons) x) 
      (seq.++ (seq.unit (ssm.cons.arg1 x)) (unpack_seq (ssm.cons.arg2 x)))
      (as seq.empty (Seq vsm.Value))))
  :pattern ((unpack_seq x))))
  :named smtx.unpack_seq.def))
  
(assert (! (forall ((T tsm.Type) (x (Seq vsm.Value)))
  (! (= (pack_seq T x) 
    (ite (> (seq.len x) 0)
      (ssm.cons (seq.nth x 0) (pack_seq T (seq.extract x 1 (- (seq.len x) 1))))
      (ssm.empty T)))
  :pattern ((pack_seq T x))))
  :named smtx.pack_seq.def))

(assert (! (forall ((x ssm.Seq))
  (! (= (unpack_string x)
    (ite ((_ is ssm.cons) x)
      (str.++ (char_of_value (ssm.cons.arg1 x)) (unpack_string (ssm.cons.arg2 x)))
      ""))
  :pattern ((unpack_string x))))
  :named smtx.unpack_string.def))

(assert (! (forall ((x String))
  (! (= (pack_string x)
    (ite (> (str.len x) 0)
      (ssm.cons (vsm.Char (str.to_code (str.substr x 0 1))) (pack_string (str.substr x 1 (- (str.len x) 1))))
      (ssm.empty tsm.Char)))
  :pattern ((pack_string x))))
  :named smtx.pack_string.def))

(assert (! (forall ((x vsm.Value))
  (! (= (char_of_value x)
    (ite ((_ is vsm.Char) x) (str.from_code (vsm.Char.arg1 x)) ""))
  :pattern ((char_of_value x))))
  :named smtx.char_of_value.def))

; models
(define-sort smk.SmtModelKey () (Tuple String tsm.Type))
(define-sort smm.SmtModel () (Array smk.SmtModelKey vsm.Value))

(define-fun teq ((x eo.Term) (y eo.Term)) Bool (= x y))
(define-fun Teq ((x tsm.Type) (y tsm.Type)) Bool (= x y))
(define-fun veq ((x vsm.Value) (y vsm.Value)) Bool (= x y))

(declare-fun thash (eo.Term) Int)
(declare-fun trevhash (Int) eo.Term)
; axiom for hash
; note: this implies that thash is injective, which implies $eo_hash is injective.
(assert (! (forall ((x eo.Term))
    (! (= (trevhash (thash x)) x) :pattern ((thash x)))) :named eo.hash_injective))
(define-fun tcmp ((a eo.Term) (b eo.Term)) Bool (< (thash a) (thash b)))

; forward declarations
(declare-fun eval_texists (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun eval_tforall (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun eval_tchoice (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun inhabited_type (tsm.Type) Bool)
(declare-fun eval_tlambda (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun eval_tapply (smm.SmtModel vsm.Value vsm.Value) vsm.Value)
; whether two (e.g. map) value are extensionally equal
(declare-fun veq_ext (msm.Map msm.Map) Bool)
  
;;; Relevant definitions

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

; fwd-decl: $eo_model_sat
(declare-fun $eo_model_sat (smm.SmtModel eo.Term) eo.Term)

; fwd-decl: $eo_model_unsat
(declare-fun $eo_model_unsat (smm.SmtModel eo.Term) eo.Term)

; program: $vsm_apply_head
(declare-fun $vsm_apply_head (vsm.Value) vsm.Value)
(assert (! (forall ((x1 vsm.Value))
  (! (= ($vsm_apply_head x1)
  (ite ((_ is vsm.Apply) x1)
    ($vsm_apply_head (vsm.Apply.arg1 x1))
    x1
)) :pattern (($vsm_apply_head x1)))) :named sm.axiom.$vsm_apply_head))

; program: $vsm_apply_arg_nth
(declare-fun $vsm_apply_arg_nth (vsm.Value Nat Nat) vsm.Value)
(assert (! (forall ((x1 vsm.Value) (x2 Nat) (x3 Nat))
  (! (= ($vsm_apply_arg_nth x1 x2 x3)
  (ite (and ((_ is vsm.Apply) x1) ((_ is nat.succ) x3))
    (ite (nateq x2 (nat.succ.arg1 x3)) (vsm.Apply.arg2 x1) ($vsm_apply_arg_nth (vsm.Apply.arg1 x1) x2 (nat.succ.arg1 x3)))
    vsm.NotValue
)) :pattern (($vsm_apply_arg_nth x1 x2 x3)))) :named sm.axiom.$vsm_apply_arg_nth))

; fwd-decl: $smtx_typeof_value
(declare-fun $smtx_typeof_value (vsm.Value) tsm.Type)

; fwd-decl: $smtx_typeof
(declare-fun $smtx_typeof (sm.Term) tsm.Type)

; fwd-decl: $smtx_model_eval
(declare-fun $smtx_model_eval (smm.SmtModel sm.Term) vsm.Value)

; fwd-decl: $smtx_model_lookup
(declare-fun $smtx_model_lookup (smm.SmtModel String tsm.Type) vsm.Value)

; fwd-decl: $smtx_model_update
(declare-fun $smtx_model_update (smm.SmtModel String tsm.Type vsm.Value) smm.SmtModel)

; program: $smtx_typeof_guard
(define-fun $smtx_typeof_guard ((x1 tsm.Type) (x2 tsm.Type)) tsm.Type
    (ite (Teq x1 tsm.None) tsm.None x2)
)

; program: $smtx_typeof_guard_inhabited
(define-fun $smtx_typeof_guard_inhabited ((x1 tsm.Type) (x2 tsm.Type)) tsm.Type
    (ite (inhabited_type x1) x2 tsm.None)
)

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

; program: $smtx_map_to_set_type
(define-fun $smtx_map_to_set_type ((x1 tsm.Type)) tsm.Type
  (ite (and ((_ is tsm.Map) x1) (= (tsm.Map.arg2 x1) tsm.Bool))
    (tsm.Set (tsm.Map.arg1 x1))
    tsm.None
))

; program: $smtx_typeof_seq_value
(declare-fun $smtx_typeof_seq_value (ssm.Seq) tsm.Type)
(assert (! (forall ((x1 ssm.Seq))
  (! (= ($smtx_typeof_seq_value x1)
  (ite ((_ is ssm.cons) x1)
    (ite (Teq (tsm.Seq ($smtx_typeof_value (ssm.cons.arg1 x1))) ($smtx_typeof_seq_value (ssm.cons.arg2 x1))) ($smtx_typeof_seq_value (ssm.cons.arg2 x1)) tsm.None)
    (tsm.Seq (ssm.empty.arg1 x1))
)) :pattern (($smtx_typeof_seq_value x1)))) :named sm.axiom.$smtx_typeof_seq_value))

; program: $smtx_dtc_num_sels
(declare-fun $smtx_dtc_num_sels (dtc.DatatypeCons) Nat)
(assert (! (forall ((x1 dtc.DatatypeCons))
  (! (= ($smtx_dtc_num_sels x1)
  (ite ((_ is dtc.cons) x1)
    (nat.succ ($smtx_dtc_num_sels (dtc.cons.arg2 x1)))
    nat.zero
)) :pattern (($smtx_dtc_num_sels x1)))) :named sm.axiom.$smtx_dtc_num_sels))

; program: $smtx_dt_num_sels
(declare-fun $smtx_dt_num_sels (dt.Datatype Nat) Nat)
(assert (! (forall ((x1 dt.Datatype) (x2 Nat))
  (! (= ($smtx_dt_num_sels x1 x2)
  (ite (and ((_ is dt.sum) x1) (= x2 nat.zero))
    ($smtx_dtc_num_sels (dt.sum.arg1 x1))
  (ite (and ((_ is dt.sum) x1) ((_ is nat.succ) x2))
    ($smtx_dt_num_sels (dt.sum.arg2 x1) (nat.succ.arg1 x2))
    nat.zero
))) :pattern (($smtx_dt_num_sels x1 x2)))) :named sm.axiom.$smtx_dt_num_sels))

; fwd-decl: $smtx_dt_substitute
(declare-fun $smtx_dt_substitute (String dt.Datatype dt.Datatype) dt.Datatype)

; program: $smtx_dtc_substitute
(declare-fun $smtx_dtc_substitute (String dt.Datatype dtc.DatatypeCons) dtc.DatatypeCons)
(assert (! (forall ((x1 String) (x2 dt.Datatype) (x3 dtc.DatatypeCons))
  (! (= ($smtx_dtc_substitute x1 x2 x3)
  (ite (and ((_ is dtc.cons) x3) ((_ is tsm.Datatype) (dtc.cons.arg1 x3)))
    (dtc.cons (tsm.Datatype (tsm.Datatype.arg1 (dtc.cons.arg1 x3)) (ite (streq x1 (tsm.Datatype.arg1 (dtc.cons.arg1 x3))) (tsm.Datatype.arg2 (dtc.cons.arg1 x3)) ($smtx_dt_substitute x1 x2 (tsm.Datatype.arg2 (dtc.cons.arg1 x3))))) ($smtx_dtc_substitute x1 x2 (dtc.cons.arg2 x3)))
  (ite ((_ is dtc.cons) x3)
    (dtc.cons (ite (Teq (dtc.cons.arg1 x3) (tsm.TypeRef x1)) (tsm.Datatype x1 x2) (dtc.cons.arg1 x3)) ($smtx_dtc_substitute x1 x2 (dtc.cons.arg2 x3)))
    dtc.unit
))) :pattern (($smtx_dtc_substitute x1 x2 x3)))) :named sm.axiom.$smtx_dtc_substitute))

; program: $smtx_dt_substitute
(assert (! (forall ((x1 String) (x2 dt.Datatype) (x3 dt.Datatype))
  (! (= ($smtx_dt_substitute x1 x2 x3)
  (ite ((_ is dt.sum) x3)
    (dt.sum ($smtx_dtc_substitute x1 x2 (dt.sum.arg1 x3)) ($smtx_dt_substitute x1 x2 (dt.sum.arg2 x3)))
    dt.null
)) :pattern (($smtx_dt_substitute x1 x2 x3)))) :named sm.axiom.$smtx_dt_substitute))

; program: $smtx_typeof_dt_cons_value_rec
(declare-fun $smtx_typeof_dt_cons_value_rec (tsm.Type dt.Datatype Nat) tsm.Type)
(assert (! (forall ((x1 tsm.Type) (x2 dt.Datatype) (x3 Nat))
  (! (= ($smtx_typeof_dt_cons_value_rec x1 x2 x3)
  (ite (and ((_ is dt.sum) x2) (= (dt.sum.arg1 x2) dtc.unit) (= x3 nat.zero))
    x1
  (ite (and ((_ is dt.sum) x2) ((_ is dtc.cons) (dt.sum.arg1 x2)) (= x3 nat.zero))
    (tsm.DtConsType (dtc.cons.arg1 (dt.sum.arg1 x2)) ($smtx_typeof_dt_cons_value_rec x1 (dt.sum (dtc.cons.arg2 (dt.sum.arg1 x2)) (dt.sum.arg2 x2)) nat.zero))
  (ite (and ((_ is dt.sum) x2) ((_ is nat.succ) x3))
    ($smtx_typeof_dt_cons_value_rec x1 (dt.sum.arg2 x2) (nat.succ.arg1 x3))
    tsm.None
)))) :pattern (($smtx_typeof_dt_cons_value_rec x1 x2 x3)))) :named sm.axiom.$smtx_typeof_dt_cons_value_rec))

; program: $smtx_typeof_dt_cons_rec
(declare-fun $smtx_typeof_dt_cons_rec (tsm.Type dt.Datatype Nat) tsm.Type)
(assert (! (forall ((x1 tsm.Type) (x2 dt.Datatype) (x3 Nat))
  (! (= ($smtx_typeof_dt_cons_rec x1 x2 x3)
  (ite (and ((_ is dt.sum) x2) (= (dt.sum.arg1 x2) dtc.unit) (= x3 nat.zero))
    x1
  (ite (and ((_ is dt.sum) x2) ((_ is dtc.cons) (dt.sum.arg1 x2)) (= x3 nat.zero))
    (tsm.DtConsType (dtc.cons.arg1 (dt.sum.arg1 x2)) ($smtx_typeof_dt_cons_rec x1 (dt.sum (dtc.cons.arg2 (dt.sum.arg1 x2)) (dt.sum.arg2 x2)) nat.zero))
  (ite (and ((_ is dt.sum) x2) ((_ is nat.succ) x3))
    ($smtx_typeof_dt_cons_rec x1 (dt.sum.arg2 x2) (nat.succ.arg1 x3))
    tsm.None
)))) :pattern (($smtx_typeof_dt_cons_rec x1 x2 x3)))) :named sm.axiom.$smtx_typeof_dt_cons_rec))

; program: $smtx_ret_typeof_sel_rec
(declare-fun $smtx_ret_typeof_sel_rec (dt.Datatype Nat Nat) tsm.Type)
(assert (! (forall ((x1 dt.Datatype) (x2 Nat) (x3 Nat))
  (! (= ($smtx_ret_typeof_sel_rec x1 x2 x3)
  (ite (and ((_ is dt.sum) x1) ((_ is dtc.cons) (dt.sum.arg1 x1)) (= x2 nat.zero) (= x3 nat.zero))
    (dtc.cons.arg1 (dt.sum.arg1 x1))
  (ite (and ((_ is dt.sum) x1) ((_ is dtc.cons) (dt.sum.arg1 x1)) (= x2 nat.zero) ((_ is nat.succ) x3))
    ($smtx_ret_typeof_sel_rec (dt.sum (dtc.cons.arg2 (dt.sum.arg1 x1)) (dt.sum.arg2 x1)) nat.zero (nat.succ.arg1 x3))
  (ite (and ((_ is dt.sum) x1) ((_ is nat.succ) x2))
    ($smtx_ret_typeof_sel_rec (dt.sum.arg2 x1) (nat.succ.arg1 x2) x3)
    tsm.None
)))) :pattern (($smtx_ret_typeof_sel_rec x1 x2 x3)))) :named sm.axiom.$smtx_ret_typeof_sel_rec))

; program: $smtx_ret_typeof_sel
(define-fun $smtx_ret_typeof_sel ((x1 String) (x2 dt.Datatype) (x3 Nat) (x4 Nat)) tsm.Type
    ($smtx_ret_typeof_sel_rec ($smtx_dt_substitute x1 x2 x2) x3 x4)
)

; program: $smtx_typeof_apply_value
(define-fun $smtx_typeof_apply_value ((x1 tsm.Type) (x2 tsm.Type)) tsm.Type
  (ite ((_ is tsm.DtConsType) x1)
    ($smtx_typeof_guard (tsm.DtConsType.arg1 x1) (ite (Teq (tsm.DtConsType.arg1 x1) x2) (tsm.DtConsType.arg2 x1) tsm.None))
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
  (ite ((_ is vsm.Binary) x1)
    (ite (zleq 0 (vsm.Binary.arg1 x1)) (tsm.BitVec (vsm.Binary.arg1 x1)) tsm.None)
  (ite ((_ is vsm.RegLan) x1)
    tsm.RegLan
  (ite ((_ is vsm.Map) x1)
    ($smtx_typeof_map_value (vsm.Map.arg1 x1))
  (ite ((_ is vsm.Set) x1)
    ($smtx_map_to_set_type ($smtx_typeof_map_value (vsm.Set.arg1 x1)))
  (ite ((_ is vsm.Seq) x1)
    ($smtx_typeof_seq_value (vsm.Seq.arg1 x1))
  (ite ((_ is vsm.Char) x1)
    tsm.Char
  (ite ((_ is vsm.DtCons) x1)
    ($smtx_typeof_dt_cons_value_rec (tsm.Datatype (vsm.DtCons.arg1 x1) (vsm.DtCons.arg2 x1)) ($smtx_dt_substitute (vsm.DtCons.arg1 x1) (vsm.DtCons.arg2 x1) (vsm.DtCons.arg2 x1)) (vsm.DtCons.arg3 x1))
  (ite ((_ is vsm.Apply) x1)
    ($smtx_typeof_apply_value ($smtx_typeof_value (vsm.Apply.arg1 x1)) ($smtx_typeof_value (vsm.Apply.arg2 x1)))
    tsm.None
)))))))))))) :pattern (($smtx_typeof_value x1)))) :named sm.axiom.$smtx_typeof_value))

; program: $smtx_model_eval_ite
(define-fun $smtx_model_eval_ite ((x1 vsm.Value) (x2 vsm.Value) (x3 vsm.Value)) vsm.Value
  (ite (and ((_ is vsm.Boolean) x1) (= (vsm.Boolean.arg1 x1) true))
    x2
  (ite (and ((_ is vsm.Boolean) x1) (= (vsm.Boolean.arg1 x1) false))
    x3
    vsm.NotValue
)))

; program: $smtx_model_eval_=
(declare-fun $smtx_model_eval_= (vsm.Value vsm.Value) vsm.Value)
(assert (! (forall ((x1 vsm.Value) (x2 vsm.Value))
  (! (= ($smtx_model_eval_= x1 x2)
  (ite (and ((_ is vsm.Map) x1) ((_ is vsm.Map) x2))
    (vsm.Boolean (veq_ext (vsm.Map.arg1 x1) (vsm.Map.arg1 x2)))
  (ite (and ((_ is vsm.Set) x1) ((_ is vsm.Set) x2))
    (vsm.Boolean (veq_ext (vsm.Set.arg1 x1) (vsm.Set.arg1 x2)))
  (ite (and ((_ is vsm.Seq) x1) ((_ is ssm.empty) (vsm.Seq.arg1 x1)) ((_ is vsm.Seq) x2) ((_ is ssm.empty) (vsm.Seq.arg1 x2)))
    (vsm.Boolean true)
  (ite (and ((_ is vsm.Seq) x1) ((_ is ssm.cons) (vsm.Seq.arg1 x1)) ((_ is vsm.Seq) x2) ((_ is ssm.cons) (vsm.Seq.arg1 x2)))
    (vsm.Boolean (and (veq ($smtx_model_eval_= (ssm.cons.arg1 (vsm.Seq.arg1 x1)) (ssm.cons.arg1 (vsm.Seq.arg1 x2))) (vsm.Boolean true)) (veq ($smtx_model_eval_= (vsm.Seq (ssm.cons.arg2 (vsm.Seq.arg1 x1))) (vsm.Seq (ssm.cons.arg2 (vsm.Seq.arg1 x2)))) (vsm.Boolean true))))
  (ite (and ((_ is vsm.Apply) x1) ((_ is vsm.Apply) x2))
    (vsm.Boolean (and (veq ($smtx_model_eval_= (vsm.Apply.arg1 x1) (vsm.Apply.arg1 x2)) (vsm.Boolean true)) (veq ($smtx_model_eval_= (vsm.Apply.arg2 x1) (vsm.Apply.arg2 x2)) (vsm.Boolean true))))
    (vsm.Boolean (veq x1 x2))
)))))) :pattern (($smtx_model_eval_= x1 x2)))) :named sm.axiom.$smtx_model_eval_=))

; program: $smtx_map_select
(define-fun $smtx_map_select ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite ((_ is vsm.Map) x1)
    ($smtx_msm_lookup (vsm.Map.arg1 x1) x2)
  (ite ((_ is vsm.Set) x1)
    ($smtx_msm_lookup (vsm.Set.arg1 x1) x2)
    vsm.NotValue
)))

; program: $smtx_model_eval_dt_sel
(define-fun $smtx_model_eval_dt_sel ((x1 smm.SmtModel) (x2 String) (x3 dt.Datatype) (x4 Nat) (x5 Nat) (x6 vsm.Value)) vsm.Value
    (ite (veq ($vsm_apply_head x6) (vsm.DtCons x2 x3 x4)) ($vsm_apply_arg_nth x6 x5 ($smtx_dt_num_sels x3 x4)) ($smtx_map_select ($smtx_map_select ($smtx_map_select ($smtx_model_lookup x1 wrong_apply_sel_id (tsm.Map tsm.Int (tsm.Map tsm.Int (tsm.Map (tsm.Datatype x2 x3) ($smtx_ret_typeof_sel x2 x3 x4 x5))))) (vsm.Numeral (nat.to_int x4))) (vsm.Numeral (nat.to_int x5))) x6))
)

; program: $smtx_model_eval_dt_tester
(define-fun $smtx_model_eval_dt_tester ((x1 String) (x2 dt.Datatype) (x3 Nat) (x4 vsm.Value)) vsm.Value
    (vsm.Boolean (veq ($vsm_apply_head x4) (vsm.DtCons x1 x2 x3)))
)

; program: $smtx_model_eval_apply
(define-fun $smtx_model_eval_apply ((x1 vsm.Value) (x2 vsm.Value)) vsm.Value
  (ite (= x2 vsm.NotValue)
    vsm.NotValue
  (ite ((_ is vsm.DtCons) x1)
    (vsm.Apply (vsm.DtCons (vsm.DtCons.arg1 x1) (vsm.DtCons.arg2 x1) (vsm.DtCons.arg3 x1)) x2)
  (ite ((_ is vsm.Apply) x1)
    (vsm.Apply (vsm.Apply (vsm.Apply.arg1 x1) (vsm.Apply.arg2 x1)) x2)
  (ite ((_ is vsm.Map) x1)
    ($smtx_map_select (vsm.Map (vsm.Map.arg1 x1)) x2)
    vsm.NotValue
)))))

; fwd-decl: $smtx_model_eval_not
(declare-fun $smtx_model_eval_not (vsm.Value) vsm.Value)

; fwd-decl: $smtx_model_eval_and
(declare-fun $smtx_model_eval_and (vsm.Value vsm.Value) vsm.Value)

; program: $smtx_model_eval_not
(assert (! (forall ((x1 vsm.Value))
  (! (= ($smtx_model_eval_not x1)
  (ite ((_ is vsm.Boolean) x1)
    (vsm.Boolean (not (vsm.Boolean.arg1 x1)))
    vsm.NotValue
)) :pattern (($smtx_model_eval_not x1)))) :named sm.axiom.$smtx_model_eval_not))

; program: $smtx_model_eval_and
(assert (! (forall ((x1 vsm.Value) (x2 vsm.Value))
  (! (= ($smtx_model_eval_and x1 x2)
  (ite (and ((_ is vsm.Boolean) x1) ((_ is vsm.Boolean) x2))
    (vsm.Boolean (and (vsm.Boolean.arg1 x1) (vsm.Boolean.arg1 x2)))
    vsm.NotValue
)) :pattern (($smtx_model_eval_and x1 x2)))) :named sm.axiom.$smtx_model_eval_and))

; program: $smtx_model_eval
(assert (! (forall ((x1 smm.SmtModel) (x2 sm.Term))
  (! (= ($smtx_model_eval x1 x2)
  (ite ((_ is sm.Boolean) x2)
    (vsm.Boolean (sm.Boolean.arg1 x2))
  (ite ((_ is sm.Numeral) x2)
    (vsm.Numeral (sm.Numeral.arg1 x2))
  (ite ((_ is sm.Rational) x2)
    (vsm.Rational (sm.Rational.arg1 x2))
  (ite ((_ is sm.String) x2)
    (vsm.Seq (pack_string (sm.String.arg1 x2)))
  (ite ((_ is sm.Binary) x2)
    (vsm.Binary (sm.Binary.arg1 x2) (sm.Binary.arg2 x2))
  (ite (and ((_ is sm.Apply) x2) (= (sm.Apply.arg1 x2) sm.not))
    ($smtx_model_eval_not ($smtx_model_eval x1 (sm.Apply.arg2 x2)))
  (ite (and ((_ is sm.Apply) x2) ((_ is sm.Apply) (sm.Apply.arg1 x2)) (= (sm.Apply.arg1 (sm.Apply.arg1 x2)) sm.and))
    ($smtx_model_eval_and ($smtx_model_eval x1 (sm.Apply.arg2 (sm.Apply.arg1 x2))) ($smtx_model_eval x1 (sm.Apply.arg2 x2)))
  (ite (and ((_ is sm.Apply) x2) ((_ is sm.Apply) (sm.Apply.arg1 x2)) ((_ is sm.Apply) (sm.Apply.arg1 (sm.Apply.arg1 x2))) (= (sm.Apply.arg1 (sm.Apply.arg1 (sm.Apply.arg1 x2))) sm.ite))
    ($smtx_model_eval_ite ($smtx_model_eval x1 (sm.Apply.arg2 (sm.Apply.arg1 (sm.Apply.arg1 x2)))) ($smtx_model_eval x1 (sm.Apply.arg2 (sm.Apply.arg1 x2))) ($smtx_model_eval x1 (sm.Apply.arg2 x2)))
  (ite (and ((_ is sm.Apply) x2) ((_ is sm.Apply) (sm.Apply.arg1 x2)) (= (sm.Apply.arg1 (sm.Apply.arg1 x2)) sm.=))
    ($smtx_model_eval_= ($smtx_model_eval x1 (sm.Apply.arg2 (sm.Apply.arg1 x2))) ($smtx_model_eval x1 (sm.Apply.arg2 x2)))
  (ite (and ((_ is sm.Apply) x2) ((_ is sm.exists) (sm.Apply.arg1 x2)))
    (eval_texists x1 (sm.exists.arg1 (sm.Apply.arg1 x2)) (sm.exists.arg2 (sm.Apply.arg1 x2)) (sm.Apply.arg2 x2))
  (ite (and ((_ is sm.Apply) x2) ((_ is sm.forall) (sm.Apply.arg1 x2)))
    (eval_tforall x1 (sm.forall.arg1 (sm.Apply.arg1 x2)) (sm.forall.arg2 (sm.Apply.arg1 x2)) (sm.Apply.arg2 x2))
  (ite (and ((_ is sm.Apply) x2) ((_ is sm.choice) (sm.Apply.arg1 x2)))
    (eval_tchoice x1 (sm.choice.arg1 (sm.Apply.arg1 x2)) (sm.choice.arg2 (sm.Apply.arg1 x2)) (sm.Apply.arg2 x2))
  (ite ((_ is sm.DtCons) x2)
    (vsm.DtCons (sm.DtCons.arg1 x2) (sm.DtCons.arg2 x2) (sm.DtCons.arg3 x2))
  (ite (and ((_ is sm.Apply) x2) ((_ is sm.DtSel) (sm.Apply.arg1 x2)))
    ($smtx_model_eval_dt_sel x1 (sm.DtSel.arg1 (sm.Apply.arg1 x2)) (sm.DtSel.arg2 (sm.Apply.arg1 x2)) (sm.DtSel.arg3 (sm.Apply.arg1 x2)) (sm.DtSel.arg4 (sm.Apply.arg1 x2)) ($smtx_model_eval x1 (sm.Apply.arg2 x2)))
  (ite (and ((_ is sm.Apply) x2) ((_ is sm.DtTester) (sm.Apply.arg1 x2)))
    ($smtx_model_eval_dt_tester (sm.DtTester.arg1 (sm.Apply.arg1 x2)) (sm.DtTester.arg2 (sm.Apply.arg1 x2)) (sm.DtTester.arg3 (sm.Apply.arg1 x2)) ($smtx_model_eval x1 (sm.Apply.arg2 x2)))
  (ite ((_ is sm.Apply) x2)
    ($smtx_model_eval_apply ($smtx_model_eval x1 (sm.Apply.arg1 x2)) ($smtx_model_eval x1 (sm.Apply.arg2 x2)))
  (ite ((_ is sm.Var) x2)
    ($smtx_model_lookup x1 (sm.Var.arg1 x2) (sm.Var.arg2 x2))
  (ite ((_ is sm.UConst) x2)
    ($smtx_model_lookup x1 (sm.UConst.arg1 x2) (sm.UConst.arg2 x2))
    vsm.NotValue
))))))))))))))))))) :pattern (($smtx_model_eval x1 x2)))) :named sm.axiom.$smtx_model_eval))

; program: $smtx_typeof_ite
(define-fun $smtx_typeof_ite ((x1 tsm.Type) (x2 tsm.Type) (x3 tsm.Type)) tsm.Type
  (ite (= x1 tsm.Bool)
    (ite (Teq x2 x3) x2 tsm.None)
    tsm.None
))

; program: $smtx_typeof_=
(define-fun $smtx_typeof_= ((x1 tsm.Type) (x2 tsm.Type)) tsm.Type
    ($smtx_typeof_guard x1 (ite (Teq x1 x2) tsm.Bool tsm.None))
)

; program: $smtx_typeof_apply
(define-fun $smtx_typeof_apply ((x1 tsm.Type) (x2 tsm.Type)) tsm.Type
  (ite ((_ is tsm.Map) x1)
    ($smtx_typeof_guard (tsm.Map.arg1 x1) (ite (Teq (tsm.Map.arg1 x1) x2) (tsm.Map.arg2 x1) tsm.None))
  (ite ((_ is tsm.DtConsType) x1)
    ($smtx_typeof_guard (tsm.DtConsType.arg1 x1) (ite (Teq (tsm.DtConsType.arg1 x1) x2) (tsm.DtConsType.arg2 x1) tsm.None))
    tsm.None
)))

; program: $smtx_typeof
(assert (! (forall ((x1 sm.Term))
  (! (= ($smtx_typeof x1)
  (ite ((_ is sm.Boolean) x1)
    tsm.Bool
  (ite ((_ is sm.Numeral) x1)
    tsm.Int
  (ite ((_ is sm.Rational) x1)
    tsm.Real
  (ite ((_ is sm.String) x1)
    (tsm.Seq tsm.Char)
  (ite ((_ is sm.Binary) x1)
    (ite (and (zleq 0 (sm.Binary.arg1 x1)) (zeq (sm.Binary.arg2 x1) (mod_total (sm.Binary.arg2 x1) (int.pow2 (sm.Binary.arg1 x1))))) (tsm.BitVec (sm.Binary.arg1 x1)) tsm.None)
  (ite (and ((_ is sm.Apply) x1) (= (sm.Apply.arg1 x1) sm.not))
    (ite (Teq ($smtx_typeof (sm.Apply.arg2 x1)) tsm.Bool) tsm.Bool tsm.None)
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) (= (sm.Apply.arg1 (sm.Apply.arg1 x1)) sm.and))
    (ite (Teq ($smtx_typeof (sm.Apply.arg2 (sm.Apply.arg1 x1))) tsm.Bool) (ite (Teq ($smtx_typeof (sm.Apply.arg2 x1)) tsm.Bool) tsm.Bool tsm.None) tsm.None)
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) ((_ is sm.Apply) (sm.Apply.arg1 (sm.Apply.arg1 x1))) (= (sm.Apply.arg1 (sm.Apply.arg1 (sm.Apply.arg1 x1))) sm.ite))
    ($smtx_typeof_ite ($smtx_typeof (sm.Apply.arg2 (sm.Apply.arg1 (sm.Apply.arg1 x1)))) ($smtx_typeof (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_typeof (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.Apply) (sm.Apply.arg1 x1)) (= (sm.Apply.arg1 (sm.Apply.arg1 x1)) sm.=))
    ($smtx_typeof_= ($smtx_typeof (sm.Apply.arg2 (sm.Apply.arg1 x1))) ($smtx_typeof (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.exists) (sm.Apply.arg1 x1)))
    (ite (Teq ($smtx_typeof (sm.Apply.arg2 x1)) tsm.Bool) tsm.Bool tsm.None)
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.forall) (sm.Apply.arg1 x1)))
    (ite (Teq ($smtx_typeof (sm.Apply.arg2 x1)) tsm.Bool) tsm.Bool tsm.None)
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.choice) (sm.Apply.arg1 x1)))
    (ite (Teq ($smtx_typeof (sm.Apply.arg2 x1)) tsm.Bool) ($smtx_typeof_guard_inhabited (sm.choice.arg2 (sm.Apply.arg1 x1)) (sm.choice.arg2 (sm.Apply.arg1 x1))) tsm.None)
  (ite ((_ is sm.DtCons) x1)
    ($smtx_typeof_dt_cons_rec (tsm.Datatype (sm.DtCons.arg1 x1) (sm.DtCons.arg2 x1)) ($smtx_dt_substitute (sm.DtCons.arg1 x1) (sm.DtCons.arg2 x1) (sm.DtCons.arg2 x1)) (sm.DtCons.arg3 x1))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.DtSel) (sm.Apply.arg1 x1)))
    ($smtx_typeof_apply (tsm.Map (tsm.Datatype (sm.DtSel.arg1 (sm.Apply.arg1 x1)) (sm.DtSel.arg2 (sm.Apply.arg1 x1))) ($smtx_ret_typeof_sel (sm.DtSel.arg1 (sm.Apply.arg1 x1)) (sm.DtSel.arg2 (sm.Apply.arg1 x1)) (sm.DtSel.arg3 (sm.Apply.arg1 x1)) (sm.DtSel.arg4 (sm.Apply.arg1 x1)))) ($smtx_typeof (sm.Apply.arg2 x1)))
  (ite (and ((_ is sm.Apply) x1) ((_ is sm.DtTester) (sm.Apply.arg1 x1)))
    ($smtx_typeof_apply (tsm.Map (tsm.Datatype (sm.DtTester.arg1 (sm.Apply.arg1 x1)) (sm.DtTester.arg2 (sm.Apply.arg1 x1))) tsm.Bool) ($smtx_typeof (sm.Apply.arg2 x1)))
  (ite ((_ is sm.Apply) x1)
    ($smtx_typeof_apply ($smtx_typeof (sm.Apply.arg1 x1)) ($smtx_typeof (sm.Apply.arg2 x1)))
  (ite ((_ is sm.Var) x1)
    ($smtx_typeof_guard_inhabited (sm.Var.arg2 x1) (sm.Var.arg2 x1))
  (ite ((_ is sm.UConst) x1)
    ($smtx_typeof_guard_inhabited (sm.UConst.arg2 x1) (sm.UConst.arg2 x1))
    tsm.None
))))))))))))))))))) :pattern (($smtx_typeof x1)))) :named sm.axiom.$smtx_typeof))

; fwd-decl: $eo_to_smt_type
(declare-fun $eo_to_smt_type (eo.Term) tsm.Type)

; program: $eo_to_smt_datatype_cons
(declare-fun $eo_to_smt_datatype_cons (edtc.DatatypeCons) dtc.DatatypeCons)
(assert (! (forall ((x1 edtc.DatatypeCons))
  (! (= ($eo_to_smt_datatype_cons x1)
  (ite (= x1 edtc.unit)
    dtc.unit
    (dtc.cons ($eo_to_smt_type (edtc.cons.arg1 x1)) ($eo_to_smt_datatype_cons (edtc.cons.arg2 x1)))
)) :pattern (($eo_to_smt_datatype_cons x1)))) :named sm.axiom.$eo_to_smt_datatype_cons))

; program: $eo_to_smt_datatype
(declare-fun $eo_to_smt_datatype (edt.Datatype) dt.Datatype)
(assert (! (forall ((x1 edt.Datatype))
  (! (= ($eo_to_smt_datatype x1)
  (ite ((_ is edt.sum) x1)
    (dt.sum ($eo_to_smt_datatype_cons (edt.sum.arg1 x1)) ($eo_to_smt_datatype (edt.sum.arg2 x1)))
    dt.null
)) :pattern (($eo_to_smt_datatype x1)))) :named sm.axiom.$eo_to_smt_datatype))

; program: $eo_to_smt_type
(assert (! (forall ((x1 eo.Term))
  (! (= ($eo_to_smt_type x1)
  (ite (= x1 eo.Bool)
    tsm.Bool
  (ite ((_ is eo.DatatypeType) x1)
    (tsm.Datatype (eo.DatatypeType.arg1 x1) ($eo_to_smt_datatype (eo.DatatypeType.arg2 x1)))
  (ite ((_ is eo.USort) x1)
    (tsm.USort (eo.USort.arg1 x1))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) ((_ is eo.FunType) (eo.Apply.arg1 (eo.Apply.arg1 x1))))
    ($smtx_typeof_guard ($eo_to_smt_type (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($smtx_typeof_guard ($eo_to_smt_type (eo.Apply.arg2 x1)) (tsm.Map ($eo_to_smt_type (eo.Apply.arg2 (eo.Apply.arg1 x1))) ($eo_to_smt_type (eo.Apply.arg2 x1)))))
  (ite (= x1 eo.Int)
    tsm.Int
  (ite (= x1 eo.Real)
    tsm.Real
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Numeral) (eo.Apply.arg2 x1)) (= (eo.Apply.arg1 x1) eo.BitVec))
    (tsm.BitVec (eo.Numeral.arg1 (eo.Apply.arg2 x1)))
  (ite (= x1 eo.Char)
    tsm.Char
  (ite (and ((_ is eo.Apply) x1) (= (eo.Apply.arg1 x1) eo.Seq))
    ($smtx_typeof_guard ($eo_to_smt_type (eo.Apply.arg2 x1)) (tsm.Seq ($eo_to_smt_type (eo.Apply.arg2 x1))))
    tsm.None
)))))))))) :pattern (($eo_to_smt_type x1)))) :named sm.axiom.$eo_to_smt_type))

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
    (sm.DtCons (eo.DtCons.arg1 x1) ($eo_to_smt_datatype (eo.DtCons.arg2 x1)) (eo.DtCons.arg3 x1))
  (ite ((_ is eo.DtSel) x1)
    (sm.DtSel (eo.DtSel.arg1 x1) ($eo_to_smt_datatype (eo.DtSel.arg2 x1)) (eo.DtSel.arg3 x1) (eo.DtSel.arg4 x1))
  (ite ((_ is eo.UConst) x1)
    (sm.UConst (uconst_id (eo.UConst.arg1 x1)) ($eo_to_smt_type (eo.UConst.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) (= (eo.Apply.arg1 x1) eo.not))
    (sm.Apply sm.not ($eo_to_smt (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) (= (eo.Apply.arg1 (eo.Apply.arg1 x1)) eo.and))
    (sm.Apply (sm.Apply sm.and ($eo_to_smt (eo.Apply.arg2 (eo.Apply.arg1 x1)))) ($eo_to_smt (eo.Apply.arg2 x1)))
  (ite (and ((_ is eo.Apply) x1) ((_ is eo.Apply) (eo.Apply.arg1 x1)) (= (eo.Apply.arg1 (eo.Apply.arg1 x1)) eo.=))
    (sm.Apply (sm.Apply sm.= ($eo_to_smt (eo.Apply.arg2 (eo.Apply.arg1 x1)))) ($eo_to_smt (eo.Apply.arg2 x1)))
  (ite ((_ is eo.Apply) x1)
    (sm.Apply ($eo_to_smt (eo.Apply.arg1 x1)) ($eo_to_smt (eo.Apply.arg2 x1)))
    sm.None
)))))))))))))) :pattern (($eo_to_smt x1)))) :named sm.axiom.$eo_to_smt))

; program: $eo_model_interprets
(define-fun $eo_model_interprets ((x1 smm.SmtModel) (x2 eo.Term) (x3 vsm.Value)) eo.Term
  (ite (= x2 eo.Stuck)
    eo.Stuck
  (ite true
    (ite (Teq ($smtx_typeof ($eo_to_smt x2)) tsm.Bool) (ite (veq ($smtx_model_eval x1 ($eo_to_smt x2)) x3) (eo.Boolean true) (eo.Boolean false)) (eo.Boolean false))
    eo.Stuck)))

; program: $eo_model_sat
(assert (! (forall ((x1 smm.SmtModel) (x2 eo.Term))
  (! (= ($eo_model_sat x1 x2)
  (ite (= x2 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_model_interprets x1 x2 (vsm.Boolean true))
    eo.Stuck))) :pattern (($eo_model_sat x1 x2)))) :named sm.axiom.$eo_model_sat))

; program: $eo_model_unsat
(assert (! (forall ((x1 smm.SmtModel) (x2 eo.Term))
  (! (= ($eo_model_unsat x1 x2)
  (ite (= x2 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_model_interprets x1 x2 (vsm.Boolean false))
    eo.Stuck))) :pattern (($eo_model_unsat x1 x2)))) :named sm.axiom.$eo_model_unsat))

; program: $eovc_symm
(define-fun $eovc_symm ((x1 eo.Term) (x2 smm.SmtModel)) eo.Term
  (ite (= x1 eo.Stuck)
    eo.Stuck
  (ite true
    ($eo_requires ($eo_model_sat x2 x1) (eo.Boolean true) ($eo_requires ($eo_model_unsat x2 ($eo_prog_symm (eo.$eo_pf x1))) (eo.Boolean true) (eo.Boolean true)))
    eo.Stuck)))



;;; Meta-level properties of models

(assert (! (forall ((M smm.SmtModel) (id String) (T tsm.Type))
  (! (= ($smtx_model_lookup M id T) (select M (tuple id T)))
  :pattern (($smtx_model_lookup M id T))))
  :named smtx.model_lookup_def))

(assert (! (forall ((M smm.SmtModel) (id String) (T tsm.Type) (v vsm.Value))
  (! (= ($smtx_model_update M id T v) (store M (tuple id T) v))
  :pattern (($smtx_model_update M id T v))))
  :named smtx.model_update_def))

; true iff there exists a value of type T that when substituted into F
; is evaluated as tgt. Note that we do not check the type of T here,
; instead $smtx_substitute will generate terms ($sm_Const v T), which
; only evaluate to v if it is of type T.
(define-fun texists_eq ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (exists ((v vsm.Value))
    (and (= ($smtx_typeof_value v) T)
         (= ($smtx_model_eval ($smtx_model_update M s T v) F) tgt))))

; true iff all values of type T when substituted into F are evaluated as tgt.
(define-fun tforall_eq ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (forall ((v vsm.Value))
    (=> (= ($smtx_typeof_value v) T)
        (= ($smtx_model_eval ($smtx_model_update M s T v) F) tgt))))

; exists
(assert (! (forall ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term))
  (! (= (eval_texists M s T F)
     (ite (texists_eq M s T F (vsm.Boolean true)) (vsm.Boolean true)
     (ite (tforall_eq M s T F (vsm.Boolean false)) (vsm.Boolean false)
       vsm.NotValue)))
  :pattern ((eval_texists M s T F))))
  :named smtx.texists.def))
  
; forall
(assert (! (forall ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term))
  (! (= (eval_tforall M s T F)
     (ite (texists_eq M s T F (vsm.Boolean false)) (vsm.Boolean false)
     (ite (tforall_eq M s T F (vsm.Boolean true)) (vsm.Boolean true)
       vsm.NotValue)))
  :pattern ((eval_tforall M s T F))))
  :named smtx.tforall.def))

; choice
; If there exists a value making the existential true, we can assume
; that substituting with choice also makes it true.
(assert (! (forall ((M smm.SmtModel) (s String) (T tsm.Type) (F sm.Term) (v vsm.Value))
  (! (=> (texists_eq M s T F (vsm.Boolean true))
      (= ($smtx_model_eval ($smtx_model_update M s T (eval_tchoice M s T F)) F)
         (vsm.Boolean true)))
  :pattern ((eval_tchoice M s T F))))
  :named smtx.tchoice.def))

; typeof choice, must be an inhabitant, else it is ill-typed.
(assert (! (forall ((T tsm.Type))
  (! (= (inhabited_type T) 
    (exists ((v vsm.Value)) (= ($smtx_typeof_value v) T)))
  :pattern ((inhabited_type T))))
  :named smtx.inhabited_type.def))
  
; whether two map values are extensionally equal
(assert (! (forall ((v1 msm.Map) (v2 msm.Map))
  (! (= (veq_ext v1 v2)
        (forall ((i vsm.Value)) (= ($smtx_msm_lookup v1 i) ($smtx_msm_lookup v2 i))))
  :pattern ((veq_ext v1 v2))))
  :named smtx.veq_ext.def))

;;; The verification condition

;;;; final verification condition for $eovc_symm
(assert (! (exists ((x1 eo.Term) (x2 smm.SmtModel))
  (= ($eovc_symm x1 x2) (eo.Boolean true))) :named sm.conjecture.$eovc_symm))
(check-sat)

