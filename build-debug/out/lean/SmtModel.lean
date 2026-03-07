import Cpc.SmtEval

set_option linter.unusedVariables false

namespace Smtm

/- SMT literal evaluation defined -/

abbrev smt_lit_Bool := SmtEval.smt_lit_Bool
abbrev smt_lit_Int := SmtEval.smt_lit_Int
abbrev smt_lit_Rat := SmtEval.smt_lit_Rat
abbrev smt_lit_String := SmtEval.smt_lit_String
abbrev smt_lit_RegLan := String --FIXME

def smt_lit_ite {T : Type} (c : smt_lit_Bool) (t e : T) : T :=
  if c then t else e
abbrev smt_lit_not := SmtEval.smt_lit_not
abbrev smt_lit_and := SmtEval.smt_lit_and
abbrev smt_lit_iff := SmtEval.smt_lit_iff
abbrev smt_lit_or := SmtEval.smt_lit_or
abbrev smt_lit_xor := SmtEval.smt_lit_xor
abbrev smt_lit_zplus := SmtEval.smt_lit_zplus
abbrev smt_lit_zmult := SmtEval.smt_lit_zmult
abbrev smt_lit_zneg := SmtEval.smt_lit_zneg
abbrev smt_lit_zeq := SmtEval.smt_lit_zeq
abbrev smt_lit_zleq := SmtEval.smt_lit_zleq
abbrev smt_lit_zlt := SmtEval.smt_lit_zlt
abbrev smt_lit_div_total := SmtEval.smt_lit_div_total
abbrev smt_lit_mod_total := SmtEval.smt_lit_mod_total
abbrev smt_lit_zexp_total := SmtEval.smt_lit_zexp_total
abbrev smt_lit_int_pow2 := SmtEval.smt_lit_int_pow2
abbrev smt_lit_piand := SmtEval.smt_lit_piand
abbrev smt_lit_mk_rational := SmtEval.smt_lit_mk_rational
abbrev smt_lit_qplus := SmtEval.smt_lit_qplus
abbrev smt_lit_qmult := SmtEval.smt_lit_qmult
abbrev smt_lit_qneg := SmtEval.smt_lit_qneg
abbrev smt_lit_qeq := SmtEval.smt_lit_qeq
abbrev smt_lit_qleq := SmtEval.smt_lit_qleq
abbrev smt_lit_qlt := SmtEval.smt_lit_qlt
abbrev smt_lit_qdiv_total := SmtEval.smt_lit_qdiv_total
abbrev smt_lit_to_int := SmtEval.smt_lit_to_int
abbrev smt_lit_to_real := SmtEval.smt_lit_to_real
abbrev smt_lit_str_len := SmtEval.smt_lit_str_len
abbrev smt_lit_str_concat := SmtEval.smt_lit_str_concat
abbrev smt_lit_str_substr := SmtEval.smt_lit_str_substr
abbrev smt_lit_str_indexof := SmtEval.smt_lit_str_indexof
abbrev smt_lit_str_to_code := SmtEval.smt_lit_str_to_code
abbrev smt_lit_str_from_code := SmtEval.smt_lit_str_from_code

abbrev smt_lit_bit := SmtEval.smt_lit_bit
abbrev smt_lit_msb := SmtEval.smt_lit_msb
abbrev smt_lit_binary_and := SmtEval.smt_lit_binary_and
abbrev smt_lit_binary_or := SmtEval.smt_lit_binary_or
abbrev smt_lit_binary_xor := SmtEval.smt_lit_binary_xor
abbrev smt_lit_binary_not := SmtEval.smt_lit_binary_not
abbrev smt_lit_binary_max := SmtEval.smt_lit_binary_max
abbrev smt_lit_binary_uts := SmtEval.smt_lit_binary_uts
abbrev smt_lit_binary_concat := SmtEval.smt_lit_binary_concat
abbrev smt_lit_binary_extract := SmtEval.smt_lit_binary_extract

-- SMT Beyond Eunoia

def smt_lit_streq : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | x, y => decide (x = y)

def smt_lit_int_log2 : smt_lit_Int -> smt_lit_Int
  | _ => 0 -- FIXME

def smt_lit_str_lt : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_from_int : smt_lit_Int -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_to_int : smt_lit_String -> smt_lit_Int
  | _ => 0 -- FIXME
def smt_lit_str_to_upper : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_to_lower : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_update : smt_lit_String -> smt_lit_Int -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_rev : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_replace : smt_lit_String -> smt_lit_String -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_replace_all : smt_lit_String -> smt_lit_String -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_contains : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_to_re : smt_lit_String -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_mult : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_plus : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_comp : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_concat : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_inter : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_diff : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_union : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_range : smt_lit_String -> smt_lit_String -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_str_in_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_indexof_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Int -> smt_lit_Int
  | _, _, _ => 0 -- FIXME
def smt_lit_str_replace_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_replace_re_all : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_re_allchar : smt_lit_RegLan := "" --FIXME
def smt_lit_re_none : smt_lit_RegLan := "" --FIXME
def smt_lit_re_all : smt_lit_RegLan := "" --FIXME

-- Partial semantics

def smt_lit_qdiv_by_zero_id : smt_lit_Int := -1
def smt_lit_div_by_zero_id : smt_lit_Int := -2
def smt_lit_mod_by_zero_id : smt_lit_Int := -3

mutual

/- 
SMT-LIB types.
-/
inductive SmtType : Type where
  | None : SmtType
  | Bool : SmtType
  | Int : SmtType
  | Real : SmtType
  | RegLan : SmtType
  | BitVec : smt_lit_Int -> SmtType
  | Map : SmtType -> SmtType -> SmtType
  | DtConsType : SmtType -> SmtType -> SmtType
  | Seq : SmtType -> SmtType
  | Char : SmtType
  | Datatype : smt_lit_String -> SmtDatatype -> SmtType
  | TypeRef : smt_lit_String -> SmtType

deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
  | None : SmtTerm
  | Boolean : smt_lit_Bool -> SmtTerm
  | Numeral : smt_lit_Int -> SmtTerm
  | Rational : smt_lit_Rat -> SmtTerm
  | String : smt_lit_String -> SmtTerm
  | Binary : smt_lit_Int -> smt_lit_Int -> SmtTerm
  | Apply : SmtTerm -> SmtTerm -> SmtTerm
  | Var : smt_lit_String -> SmtType -> SmtTerm
  | exists : smt_lit_String -> SmtType -> SmtTerm
  | forall : smt_lit_String -> SmtType -> SmtTerm
  | lambda : smt_lit_String -> SmtType -> SmtTerm
  | choice : smt_lit_String -> SmtType -> SmtTerm
  | DtCons : smt_lit_String -> SmtDatatype -> smt_lit_Int -> SmtTerm
  | DtSel : smt_lit_String -> SmtDatatype -> smt_lit_Int -> smt_lit_Int -> SmtTerm
  | DtTester : smt_lit_String -> SmtDatatype -> smt_lit_Int -> SmtTerm
  | DtUpdater : smt_lit_String -> SmtDatatype -> smt_lit_Int -> smt_lit_Int -> SmtTerm
  | Const : SmtValue -> SmtType -> SmtTerm
  | UConst : smt_lit_Int -> SmtType -> SmtTerm
  | not : SmtTerm
  | and : SmtTerm
  | eq : SmtTerm

deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB values.
-/
inductive SmtValue : Type where
  | NotValue : SmtValue
  | Boolean : smt_lit_Bool -> SmtValue
  | Numeral : smt_lit_Int -> SmtValue
  | Rational : smt_lit_Rat -> SmtValue
  | String : smt_lit_String -> SmtValue
  | Binary : smt_lit_Int -> smt_lit_Int -> SmtValue
  | Map : SmtMap -> SmtValue
  | Seq : SmtSeq -> SmtValue
  | RegLan : smt_lit_RegLan -> SmtValue
  | Lambda : smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | DtCons : smt_lit_String -> SmtDatatype -> smt_lit_Int -> SmtValue
  | Apply : SmtValue -> SmtValue -> SmtValue

deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB map values.
-/
inductive SmtMap : Type where
  | cons : SmtValue -> SmtValue -> SmtMap -> SmtMap
  | default : SmtType -> SmtValue -> SmtMap
deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB sequence values.
-/
inductive SmtSeq : Type where
  | cons : SmtValue -> SmtSeq -> SmtSeq
  | empty : SmtType -> SmtSeq
deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB datatypes.
-/
inductive SmtDatatype : Type where
  | null : SmtDatatype
  | sum : SmtDatatypeCons -> SmtDatatype -> SmtDatatype
deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB datatype constructors.
-/
inductive SmtDatatypeCons : Type where
  | unit : SmtDatatypeCons
  | cons : SmtType -> SmtDatatypeCons -> SmtDatatypeCons
deriving Repr, DecidableEq, Inhabited

end

/-
SMT-LIB model
-/
abbrev SmtModel := Int -- FIXME

def __smtx_model_lookup : SmtModel -> smt_lit_Int -> SmtType -> SmtValue
  | _, _, _ => (SmtValue.Boolean true) -- FIXME


/- Type equality -/
def smt_lit_Teq : SmtType -> SmtType -> smt_lit_Bool
  | x, y => decide (x = y)
/- Value equality -/
def smt_lit_veq : SmtValue -> SmtValue -> smt_lit_Bool
  | x, y => decide (x = y)
/- Used for ordering values -/
def __smtx_value_hash : SmtValue -> smt_lit_Int
  | _ => 0 -- FIXME
  
/- exists -/
def smt_lit_tforall : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME
/- forall -/
def smt_lit_texists : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME
/- choice -/
def smt_lit_tchoice : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME

/- Definition of SMT-LIB model semantics -/

mutual

partial def __vsm_apply_head : SmtValue -> SmtValue
  | (SmtValue.Apply f a) => (__vsm_apply_head f)
  | a => a


partial def __vsm_apply_arg_nth : SmtValue -> smt_lit_Int -> SmtValue
  | (SmtValue.Apply f a), n => (smt_lit_ite (smt_lit_zeq n 0) a (__vsm_apply_arg_nth f (smt_lit_zplus n (smt_lit_zneg 1))))
  | a, n => SmtValue.NotValue


partial def __smtx_msm_lookup : SmtMap -> SmtValue -> SmtValue
  | (SmtMap.cons j e m), i => (smt_lit_ite (smt_lit_veq j i) e (__smtx_msm_lookup m i))
  | (SmtMap.default T e), i => e


partial def __smtx_typeof_map_value : SmtMap -> SmtType
  | (SmtMap.cons i e m) => (smt_lit_ite (smt_lit_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e)) (__smtx_typeof_map_value m)) (__smtx_typeof_map_value m) SmtType.None)
  | (SmtMap.default T e) => (SmtType.Map T (__smtx_typeof_value e))


partial def __smtx_index_typeof_map : SmtType -> SmtType
  | (SmtType.Map T U) => T
  | T => SmtType.None


partial def __smtx_typeof_seq_value : SmtSeq -> SmtType
  | (SmtSeq.cons v vs) => (smt_lit_ite (smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)) (__smtx_typeof_seq_value vs) SmtType.None)
  | (SmtSeq.empty T) => (SmtType.Seq T)


partial def __smtx_dtc_substitute (s : smt_lit_String) (d : SmtDatatype) : SmtDatatypeCons -> SmtDatatypeCons
  | (SmtDatatypeCons.cons T c) => (SmtDatatypeCons.cons (smt_lit_ite (smt_lit_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T) (__smtx_dtc_substitute s d c))
  | SmtDatatypeCons.unit => SmtDatatypeCons.unit


partial def __smtx_dt_substitute (s : smt_lit_String) (d : SmtDatatype) : SmtDatatype -> SmtDatatype
  | (SmtDatatype.sum c d2) => (SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d d2))
  | SmtDatatype.null => SmtDatatype.null


partial def __smtx_typeof_dt_cons_value_rec (T : SmtType) : SmtDatatype -> smt_lit_Int -> SmtType
  | SmtDatatype.null, 0 => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), 0 => (SmtType.DtConsType U (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) 0))
  | (SmtDatatype.sum c d), n => (__smtx_typeof_dt_cons_value_rec T d (smt_lit_zplus n (smt_lit_zneg 1)))
  | d, n => SmtType.None


partial def __smtx_typeof_apply_value : SmtType -> SmtType -> SmtType
  | (SmtType.DtConsType T U), V => (smt_lit_ite (smt_lit_Teq T V) U SmtType.None)
  | T, U => SmtType.None


partial def __smtx_typeof_value : SmtValue -> SmtType
  | (SmtValue.Boolean b) => SmtType.Bool
  | (SmtValue.Numeral n) => SmtType.Int
  | (SmtValue.Rational q) => SmtType.Real
  | (SmtValue.String s) => (SmtType.Seq SmtType.Char)
  | (SmtValue.Binary w n) => (smt_lit_ite (smt_lit_zleq 0 w) (SmtType.BitVec w) SmtType.None)
  | (SmtValue.RegLan r) => SmtType.RegLan
  | (SmtValue.Map m) => (__smtx_typeof_map_value m)
  | (SmtValue.Seq ss) => (__smtx_typeof_seq_value ss)
  | (SmtValue.DtCons s d n) => (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n)
  | (SmtValue.Apply f v) => (__smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v))
  | v => SmtType.None


partial def __smtx_model_eval_eq (t1 : SmtValue) (t2 : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) (__smtx_typeof_value t2)) (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) SmtType.None) SmtValue.NotValue (SmtValue.Boolean (smt_lit_veq t1 t2))) SmtValue.NotValue)

partial def __smtx_map_select : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m), i => (smt_lit_ite (smt_lit_Teq (__smtx_index_typeof_map (__smtx_typeof_map_value m)) (__smtx_typeof_value i)) (__smtx_msm_lookup m i) SmtValue.NotValue)
  | v, i => SmtValue.NotValue


partial def __smtx_model_eval_dt_cons (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Int) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n) SmtType.None) SmtValue.NotValue (SmtValue.DtCons s d n))

partial def __smtx_model_eval_dt_sel (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Int) (m : smt_lit_Int) (v1 : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v1) (SmtType.Datatype s d)) (smt_lit_ite (smt_lit_veq (__vsm_apply_head v1) (SmtValue.DtCons s d n)) (__vsm_apply_arg_nth v1 m) SmtValue.NotValue) SmtValue.NotValue)

partial def __smtx_model_eval_dt_tester (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Int) (v1 : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v1) (SmtType.Datatype s d)) (SmtValue.Boolean (smt_lit_veq (__vsm_apply_head v1) (SmtValue.DtCons s d n))) SmtValue.NotValue)

partial def __smtx_model_eval_dt_updater (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Int) (m : smt_lit_Int) (v1 : SmtValue) (v2 : SmtValue) : SmtValue :=
  SmtValue.NotValue

partial def __smtx_model_eval_apply : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Apply f v), i => (SmtValue.Apply (SmtValue.Apply f v) i)
  | (SmtValue.Map m), i => (__smtx_map_select (SmtValue.Map m) i)
  | v, i => SmtValue.NotValue


partial def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (smt_lit_not x1))
  | t1 => SmtValue.NotValue


partial def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_and x1 x2))
  | t1, t2 => SmtValue.NotValue


partial def __smtx_model_eval (M : SmtModel) : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Rational r) => (SmtValue.Rational r)
  | (SmtTerm.String s) => (SmtValue.String s)
  | (SmtTerm.Binary w n) => (smt_lit_ite (smt_lit_and (smt_lit_zleq 0 w) (smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)))) (SmtValue.Binary w n) SmtValue.NotValue)
  | (SmtTerm.Apply SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x1) x2) => (__smtx_model_eval_and (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) => (__smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.exists s T) x1) => (smt_lit_tforall M s T x1)
  | (SmtTerm.Apply (SmtTerm.forall s T) x1) => (smt_lit_texists M s T x1)
  | (SmtTerm.Apply (SmtTerm.lambda s T) x1) => (SmtValue.Lambda s T x1)
  | (SmtTerm.Apply (SmtTerm.choice s T) x1) => (smt_lit_tchoice M s T x1)
  | (SmtTerm.DtCons s d n) => (__smtx_model_eval_dt_cons s d n)
  | (SmtTerm.Apply (SmtTerm.DtSel s d n m) x1) => (__smtx_model_eval_dt_sel s d n m (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.DtTester s d n) x1) => (__smtx_model_eval_dt_tester s d n (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.DtUpdater s d n m) x1) x2) => (__smtx_model_eval_dt_updater s d n m (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply f x1) => (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x1))
  | (SmtTerm.Const v T) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v) T) v SmtValue.NotValue)
  | (SmtTerm.UConst n T) => (__smtx_model_lookup M n T)
  | x1 => SmtValue.NotValue




end

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_interprets : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, (__smtx_model_eval M t) = (SmtValue.Boolean true)) ->
      smt_interprets t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, (__smtx_model_eval M t) = (SmtValue.Boolean false))->
      smt_interprets t false

/- FIXME inductive smt_model_well_typed : SmtModel -> Prop, based on smt axiom -/

/- ---------------------------------------------- -/

end Smtm
