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
$SM_EO_TERM_DECL$
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
$SM_VALUE_DECL$
  )
  (
$SM_MAP_DECL$
  )
  (
$SM_SEQ_DECL$
  )
  (
$SM_TERM_DECL$
  )
  (
$SM_TYPE_DECL$
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
(declare-fun eval_tlambda (smm.SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun eval_tapply (smm.SmtModel vsm.Value vsm.Value) vsm.Value)
; whether two (e.g. map) value are extensionally equal
(declare-fun veq_ext (vsm.Value vsm.Value) vsm.Value)
  
;;; Relevant definitions

$SM_DEFS$

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

; whether two values are extensionally equal
(assert (! (forall ((v1 vsm.Value) (v2 vsm.Value))
  (! (= (veq_ext v1 v2)
        (ite (and ((_ is vsm.Map) v1) ((_ is vsm.Map) v2))
          (vsm.Boolean (forall ((i vsm.Value)) (= ($smtx_model_eval_apply v1 i) ($smtx_model_eval_apply v2 i))))
          (vsm.Boolean (veq v1 v2))))
  :pattern ((veq_ext v1 v2))))
  :named smtx.veq_ext.def))

;;; The verification condition

$SMT_VC$
