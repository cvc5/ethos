(set-logic ALL)

; $ The part of the native layer that SMT-LIB alone gives, i.e. what the
; $ compilation of the input reached of it that names none of the datatypes
; $ of the embedding, see ethos::NativeLayer.
$NATIVE_DEFS$

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
; regular language values are the builtin SMT-LIB sort
(define-sort SmtRegLan () RegLan)

(declare-datatypes
  ((eo.Term 0) (DatatypeDecl 0)  (Datatype 0) (DatatypeCons 0)
   (vsm.Value 0) (msm.Map 0) (ssm.Seq 0) (sm.Term 0) (tsm.Type 0)
   (SmtDatatypeDecl 0) (SmtDatatype 0) (SmtDatatypeCons 0))
  (
  (
$SM_EO_TERM_DECL$
  )
  (
  (edd.nil)
  (edd.cons (edd.cons.arg1 String) (edd.cons.arg2 Datatype) (edd.cons.arg3 DatatypeDecl))
  )
  (
  (edt.null)
  (edt.sum (edt.sum.arg1 DatatypeCons) (edt.sum.arg2 Datatype))
  )
  (
  (edtc.unit)
  (edtc.cons (edtc.cons.arg1 eo.Term) (edtc.cons.arg2 DatatypeCons))
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
  (dd.nil)
  (dd.cons (dd.cons.arg1 String) (dd.cons.arg2 SmtDatatype) (dd.cons.arg3 SmtDatatypeDecl))
  )
  (
  (dt.null)
  (dt.sum (dt.sum.arg1 SmtDatatypeCons) (dt.sum.arg2 SmtDatatype))
  )
  (
  (dtc.unit)
  (dtc.cons (dtc.cons.arg1 tsm.Type) (dtc.cons.arg2 SmtDatatypeCons))
  )
  )
)

; $ The part of the native layer written over the datatypes above, which is
; $ why it comes out here rather than at the top of the file.
$NATIVE_EMBED_DEFS$

; models
(define-sort SmtModelKey () (Tuple Bool String tsm.Type))
(define-sort SmtModel () (Array SmtModelKey vsm.Value))

(declare-datatype srl.RefList
  ((reflist_nil) (reflist_insert (reflist_insert.arg1 srl.RefList) (reflist_insert.arg2 String))))

(declare-fun reflist_contains (srl.RefList String) Bool)
(assert (! (forall ((rl srl.RefList) (s String))
  (! (= (reflist_contains rl s)
    (ite ((_ is reflist_nil) rl) false
    (ite (= (reflist_insert.arg2 rl) s) true
      (reflist_contains (reflist_insert.arg1 rl) s))))
  :pattern ((reflist_contains rl s))))
  :named smtx.reflist_contains_def))

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
(declare-fun model_lookup (SmtModel String tsm.Type) vsm.Value)
(declare-fun model_var_lookup (SmtModel String tsm.Type) vsm.Value)
(declare-fun model_push (SmtModel String tsm.Type vsm.Value) SmtModel)
(declare-fun eval_exists (SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun eval_forall (SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun eval_choice (SmtModel String tsm.Type sm.Term) vsm.Value)
(declare-fun inhabited_type (tsm.Type) Bool)
(declare-fun eval_fun_apply (SmtModel String tsm.Type tsm.Type vsm.Value) vsm.Value)
; whether two (e.g. map) value are extensionally equal
(declare-fun veq_ext (msm.Map msm.Map) Bool)

;;; Relevant definitions

$SM_DEFS$

;;; Meta-level properties of models

(assert (! (forall ((M SmtModel) (id String) (T tsm.Type))
  (! (= (model_lookup M id T) (select M (tuple false id T)))
  :pattern ((model_lookup M id T))))
  :named smtx.model_lookup_def))

(assert (! (forall ((M SmtModel) (id String) (T tsm.Type))
  (! (= (model_var_lookup M id T) (select M (tuple true id T)))
  :pattern ((model_var_lookup M id T))))
  :named smtx.model_var_lookup_def))

(assert (! (forall ((M SmtModel) (id String) (T tsm.Type) (v vsm.Value))
  (! (= (model_push M id T v) (store M (tuple true id T) v))
  :pattern ((model_push M id T v))))
  :named smtx.model_update_def))

; true iff there exists a value of type T that when substituted into F
; is evaluated as tgt. Note that we do not check the type of T here,
; instead $smtx_substitute will generate terms ($sm_Const v T), which
; only evaluate to v if it is of type T.
(define-fun texists_eq ((M SmtModel) (s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (exists ((v vsm.Value))
    (and (= ($smtx_typeof_value v) T)
         (= ($smtx_model_eval (model_push M s T v) F) tgt))))

; true iff all values of type T when substituted into F are evaluated as tgt.
(define-fun tforall_eq ((M SmtModel) (s String) (T tsm.Type) (F sm.Term) (tgt vsm.Value)) Bool
  (forall ((v vsm.Value))
    (=> (= ($smtx_typeof_value v) T)
        (= ($smtx_model_eval (model_push M s T v) F) tgt))))

; exists
(assert (! (forall ((M SmtModel) (s String) (T tsm.Type) (F sm.Term))
  (! (= (eval_exists M s T F)
     (ite (texists_eq M s T F (vsm.Boolean true)) (vsm.Boolean true)
     (ite (tforall_eq M s T F (vsm.Boolean false)) (vsm.Boolean false)
       vsm.NotValue)))
  :pattern ((eval_exists M s T F))))
  :named smtx.texists.def))

; forall
(assert (! (forall ((M SmtModel) (s String) (T tsm.Type) (F sm.Term))
  (! (= (eval_forall M s T F)
     (ite (texists_eq M s T F (vsm.Boolean false)) (vsm.Boolean false)
     (ite (tforall_eq M s T F (vsm.Boolean true)) (vsm.Boolean true)
       vsm.NotValue)))
  :pattern ((eval_forall M s T F))))
  :named smtx.tforall.def))

; choice
; If there exists a value making the existential true, we can assume
; that substituting with choice also makes it true.
(assert (! (forall ((M SmtModel) (s String) (T tsm.Type) (F sm.Term) (v vsm.Value))
  (! (=> (texists_eq M s T F (vsm.Boolean true))
      (= ($smtx_model_eval (model_push M s T (eval_choice M s T F)) F)
         (vsm.Boolean true)))
  :pattern ((eval_choice M s T F))))
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
        (forall ((i vsm.Value)) (= ($smtx_map_lookup v1 i) ($smtx_map_lookup v2 i))))
  :pattern ((veq_ext v1 v2))))
  :named smtx.veq_ext.def))

; FIXME
;(assert (! (forall ((v1 msm.Map) (v2 msm.Map))
;  (! (= (eval_map_diff v1 v2)
;        (forall ((i vsm.Value)) (= ($smtx_map_lookup v1 i) ($smtx_map_lookup v2 i))))
;  :pattern ((veq_ext v1 v2))))
;  :named smtx.veq_ext.def))

;;; What a verification condition asks of the model

; The formula a term denotes evaluates, under the model M, to the value v.
; A term the model gives no type of Bool to answers no. This is the only place
; that says what the two below mean: the EO layer declares them and never
; defines them, so that the model itself has nothing to say about how a proof
; rule is verified.
(define-fun $eo_model_interprets ((M SmtModel) (F eo.Term) (v vsm.Value)) eo.Term
  (eo.Boolean (and (Teq ($smtx_typeof ($eo_to_smt F)) tsm.Bool)
                   (veq ($smtx_model_eval M ($eo_to_smt F)) v))))

(assert (! (forall ((M SmtModel) (F eo.Term))
  (! (= ($eo_model_sat M F) ($eo_model_interprets M F (vsm.Boolean true)))
  :pattern (($eo_model_sat M F))))
  :named eo.model_sat.def))

(assert (! (forall ((M SmtModel) (F eo.Term))
  (! (= ($eo_model_unsat M F) ($eo_model_interprets M F (vsm.Boolean false)))
  :pattern (($eo_model_unsat M F))))
  :named eo.model_unsat.def))

;;; The verification condition

$SMT_VC$
