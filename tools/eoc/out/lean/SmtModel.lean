module

public import Cpc.SmtValueOrder
import all Cpc.SmtValueOrder

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

abbrev SmtNativeFun := SmtValue -> SmtValue

-- A datatype declaration is checked against the list of references it may
-- name, which only the published tree builds, so the list is kept whatever
-- this compilation reaches.

-- The part of the native layer that the SMT-LIB value embedding is what
-- decides, and so cannot come out above this file, together with whatever of
-- the rest only this file reaches. See LeanMetaReduce::placeNativeDefs.
def native_char_valid (c : native_Char) : native_Bool :=
  c < 196608

def native_string_valid (s : native_String) : native_Bool :=
  s.all native_char_valid

def native_string_prefix_eq : native_String -> native_String -> native_Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: cs, d :: ds => decide (c = d) && native_string_prefix_eq cs ds

    -- compare a.num / a.den vs b.num / b.den by cross-multiplication

def native_or : native_Bool -> native_Bool -> native_Bool
  | x, y => x || y

def native_zleq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x <= y)

def native_int_to_nat (x : native_Int) : native_Nat :=
  (Int.toNat x)

def native_nat_to_int (x : native_Nat) : native_Int :=
  (Int.ofNat x)

def native_nateq : native_Nat -> native_Nat -> native_Bool
  | x, y => decide (x = y)

abbrev RefList := List native_String

def native_reflist_nil : RefList := []
def native_reflist_insert (xs : RefList) (s : native_String) := (s :: xs)
def native_reflist_contains (xs : RefList) (s : native_String ) :=
  decide (s ∈ xs)

def native_wrong_apply_sel_id (n m : native_Nat) : native_String :=
  (native_string_lit "@wrong_apply_sel_") ++ (native_string_lit (toString n)) ++ (native_string_lit "_") ++ (native_string_lit (toString m))

def native_uconst_id : native_Nat -> native_String
  | i => (native_string_lit "@u.") ++ (native_string_lit (toString i))

def native_reserved_datatype_name (s : native_String) : native_Bool :=
  native_string_prefix_eq (native_string_lit "@") s

def native_default_fun_id : native_String := (native_string_lit "@native_default_fun")

/- SMT-LIB model -/
structure SmtModelKey where
  isVar : native_Bool
  name : native_String
  ty : SmtType
deriving Repr, DecidableEq, Inhabited

structure SmtModel where
  values : SmtModelKey -> SmtValue
  nativeFuns : SmtModelKey -> SmtNativeFun
deriving Inhabited

def native_model_key (s : native_String) (T : SmtType) : SmtModelKey :=
  { isVar := false, name := s, ty := T }

def native_model_var_lookup (M : SmtModel) (s : native_String) (T : SmtType) : SmtValue :=
  M.values { isVar := true, name := s, ty := T }

def native_model_lookup (M : SmtModel) (s : native_String) (T : SmtType) : SmtValue :=
  M.values (native_model_key s T)

def native_model_push (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) : SmtModel :=
  { M with values := fun k =>
      if k = { isVar := true, name := s, ty := T } then
        v
      else
        M.values k }

def native_model_fun_lookup (M : SmtModel) (fid : native_String) (T U : SmtType) : SmtNativeFun :=
  M.nativeFuns (native_model_key fid (SmtType.FunType T U))

-- The reference lists are not reached by any signature compiled so far: they
-- are for the translation proofs of the package the published tree is
-- installed into, which this compiler never sees. So they are roots rather
-- than definitions the compilation has to reach.

/- Type equality -/
def native_Teq : SmtType -> SmtType -> native_Bool
  | x, y => decide (x = y)

/- Value equality -/
def native_veq : SmtValue -> SmtValue -> native_Bool
  | x, y => decide (x = y)

/- Value comparsion -/
def native_vcmp (v1 : SmtValue) (v2 : SmtValue) : native_Bool :=
  SmtValueOrder.lt v1 v2

-- SMT Beyond Eunoia

/-- Whether a base element of a regular language is a valid character value.
This is the well-formedness condition on base elements: a well-formed
(canonical) regular language contains only valid characters (see
native_re_canonical). Matching against a base element (.char) is structural
equality on values, which allows regular languages over arbitrary value
sequences; the sequence pattern operators (e.g. seq.replace_all) are
evaluated via singleton regular expressions over their pattern. The
allchar and range constructors match valid characters only. -/
def native_re_elem_valid : SmtValue -> native_Bool
  | (SmtValue.Char c) => native_char_valid c
  | _ => false

/-- Character ordering on base elements; only characters are comparable. -/
def native_re_elem_le : SmtValue -> SmtValue -> native_Bool
  | (SmtValue.Char c₁), (SmtValue.Char c₂) => c₁ <= c₂
  | _, _ => false

/-- The embedding of native strings as value sequences. -/
def native_string_to_values (s : native_String) : List SmtValue :=
  s.map SmtValue.Char

/-- Whether a value sequence denotes a valid string, i.e. all of its
elements are valid character values. -/
def native_re_str_valid (xs : List SmtValue) : native_Bool :=
  xs.all native_re_elem_valid

def native_re_nullable : SmtRegLan -> native_Bool
  | .empty => false
  | .epsilon => true
  | .char _ => false
  | .range _ _ => false
  | .allchar => false
  | .concat r₁ r₂ => native_re_nullable r₁ && native_re_nullable r₂
  | .union r₁ r₂ => native_re_nullable r₁ || native_re_nullable r₂
  | .inter r₁ r₂ => native_re_nullable r₁ && native_re_nullable r₂
  | .star _ => true
  | .comp r => !(native_re_nullable r)

def native_re_concat (r₁ r₂ : SmtRegLan) : SmtRegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r₁, r₂ => .concat r₁ r₂

def native_re_union (r₁ r₂ : SmtRegLan) : SmtRegLan :=
  match r₁, r₂ with
  | .empty, r => r
  | r, .empty => r
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .union r₁ r₂

def native_re_inter (r₁ r₂ : SmtRegLan) : SmtRegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .inter r₁ r₂

def native_re_comp : SmtRegLan -> SmtRegLan
  | .comp r => r
  | r => .comp r

def native_re_deriv (c : SmtValue) : SmtRegLan -> SmtRegLan
  | .empty => .empty
  | .epsilon => .empty
  | .char d => if c = d then .epsilon else .empty
  | .range lo hi =>
      if native_re_elem_valid c && native_re_elem_valid lo && native_re_elem_valid hi
          && native_re_elem_le lo c && native_re_elem_le c hi then
        .epsilon
      else
        .empty
  | .allchar => if native_re_elem_valid c then .epsilon else .empty
  | .concat r₁ r₂ =>
      native_re_union
        (native_re_concat (native_re_deriv c r₁) r₂)
        (if native_re_nullable r₁ then native_re_deriv c r₂ else .empty)
  | .union r₁ r₂ => native_re_union (native_re_deriv c r₁) (native_re_deriv c r₂)
  | .inter r₁ r₂ => native_re_inter (native_re_deriv c r₁) (native_re_deriv c r₂)
  | .star r => native_re_concat (native_re_deriv c r) (.star r)
  | .comp r => native_re_comp (native_re_deriv c r)

def native_str_in_re : List SmtValue -> SmtRegLan -> native_Bool
  | s, r =>
      if native_re_str_valid s then
        native_re_nullable <| s.foldl (fun acc c => native_re_deriv c acc) r
      else
        false

def native_re_none : SmtRegLan := .empty

def native_re_canonical : SmtRegLan -> native_Bool
  | .empty => true
  | .epsilon => true
  | .char c => native_re_elem_valid c
  | .range lo hi => native_re_elem_valid lo && native_re_elem_valid hi
  | .allchar => true
  | .concat r₁ r₂ => native_re_canonical r₁ && native_re_canonical r₂
  | .union r₁ r₂ => native_re_canonical r₁ && native_re_canonical r₂
  | .inter r₁ r₂ => native_re_canonical r₁ && native_re_canonical r₂
  | .star r => native_re_canonical r
  | .comp r => native_re_canonical r

macro_rules
  | `(native_re_ext_eq $r1 $r2) => do
      let strInReId := Lean.mkIdent `native_str_in_re
      let validId := Lean.mkIdent `native_string_valid
      let toValuesId := Lean.mkIdent `native_string_to_values
      `(by
          classical
          exact
            if hExt :
                ∀ s : native_String,
                  $validId s = true ->
                    $strInReId ($toValuesId s) $r1 = $strInReId ($toValuesId s) $r2 then
              true
            else
              false)

macro_rules
  | `(native_eval_texists $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `native_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      let canonId := Lean.mkIdent `__smtx_value_canonical_bool
      `(by
          classical
          exact
            if h :
                ∃ v : SmtValue,
                  $typeofValueId v = $T ∧
                    $canonId v = true ∧
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              SmtValue.Boolean true
            else
              SmtValue.Boolean false)

macro_rules
  | `(native_eval_tforall $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `native_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      let canonId := Lean.mkIdent `__smtx_value_canonical_bool
      `(by
          classical
          exact
            if h :
                ∀ v : SmtValue,
                  $typeofValueId v = $T ->
                    $canonId v = true ->
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              SmtValue.Boolean true
            else
              SmtValue.Boolean false)

macro_rules
  | `(native_eval_tchoice $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `native_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      let canonId := Lean.mkIdent `__smtx_value_canonical_bool
      `(by
          classical
          exact
            if hSat :
                ∃ v : SmtValue,
                  $typeofValueId v = $T ∧
                    $canonId v = true ∧
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              Classical.choose hSat
            else if hTy : ∃ v : SmtValue, $typeofValueId v = $T ∧ $canonId v then
              Classical.choose hTy
            else
              SmtValue.NotValue)


/- Definition of SMT-LIB model semantics -/

noncomputable section

mutual

def native_inhabited_type (T : SmtType) : native_Bool :=
  (native_and
    (native_not (native_Teq T SmtType.None))
    (native_Teq (__smtx_typeof_value (__smtx_type_default T)) T))

def __vsm_apply_head : SmtValue -> SmtValue
  | (SmtValue.Apply f a) => (__vsm_apply_head f)
  | a => a


def __vsm_apply_arg_nth : SmtValue -> native_Nat -> native_Nat -> SmtValue
  | (SmtValue.Apply f a), n, (native_nat_succ npos) => (native_ite (native_nateq n npos) a (__vsm_apply_arg_nth f n npos))
  | a, n, npos => SmtValue.NotValue


def __smtx_dtc_resolve : SmtDatatypeCons -> SmtDatatypeDecl -> SmtDatatypeCons
  | (SmtDatatypeCons.cons (SmtType.TypeRef s) c), dd => (SmtDatatypeCons.cons (SmtType.Datatype s dd) (__smtx_dtc_resolve c dd))
  | (SmtDatatypeCons.cons T c), dd => (SmtDatatypeCons.cons T (__smtx_dtc_resolve c dd))
  | SmtDatatypeCons.unit, dd => SmtDatatypeCons.unit


def __smtx_dt_resolve : SmtDatatype -> SmtDatatypeDecl -> SmtDatatype
  | (SmtDatatype.sum c d), dd => (SmtDatatype.sum (__smtx_dtc_resolve c dd) (__smtx_dt_resolve d dd))
  | SmtDatatype.null, dd => SmtDatatype.null


def __smtx_dd_lookup (s : native_String) : SmtDatatypeDecl -> SmtDatatype
  | (SmtDatatypeDecl.cons s2 d dd) => (native_ite (native_streq s s2) d (__smtx_dd_lookup s dd))
  | SmtDatatypeDecl.nil => SmtDatatype.null


def __smtx_dd_has_dt (s : native_String) : SmtDatatypeDecl -> native_Bool
  | (SmtDatatypeDecl.cons s2 d dd) => (native_or (native_streq s s2) (__smtx_dd_has_dt s dd))
  | SmtDatatypeDecl.nil => false


def __smtx_dt_cons_wf_rec (dd : SmtDatatypeDecl) : SmtDatatypeCons -> native_Bool
  | (SmtDatatypeCons.cons (SmtType.TypeRef s) c) => (native_and (__smtx_dd_has_dt s dd) (__smtx_dt_cons_wf_rec dd c))
  | (SmtDatatypeCons.cons T c) => (native_and (native_and (native_inhabited_type T) (__smtx_type_wf_rec T)) (__smtx_dt_cons_wf_rec dd c))
  | SmtDatatypeCons.unit => true


def __smtx_dt_wf_rec (dd : SmtDatatypeDecl) : SmtDatatype -> native_Bool
  | (SmtDatatype.sum cF dF) => (native_and (__smtx_dt_cons_wf_rec dd cF) (__smtx_dt_wf_rec dd dF))
  | SmtDatatype.null => true


def __smtx_decl_wf_rec (dd : SmtDatatypeDecl) : SmtDatatypeDecl -> native_Bool
  | (SmtDatatypeDecl.cons s d ddF) => (native_and (__smtx_dt_wf_rec dd d) (native_and (native_inhabited_type (SmtType.Datatype s dd)) (native_and (__smtx_decl_wf_rec dd ddF) (native_not (__smtx_dd_has_dt s ddF)))))
  | SmtDatatypeDecl.nil => true


def __smtx_type_wf_rec : SmtType -> native_Bool
  | (SmtType.Datatype s dd) => (native_and (__smtx_dd_has_dt s dd) (__smtx_decl_wf_rec dd dd))
  | (SmtType.TypeRef s) => false
  | (SmtType.FunType x1 x2) => false
  | (SmtType.DtcAppType x1 x2) => false
  | SmtType.None => false
  | SmtType.RegLan => false
  | (SmtType.Map x1 x2) => (native_and (native_and (native_inhabited_type x1) (__smtx_type_wf_rec x1)) (native_and (native_inhabited_type x2) (__smtx_type_wf_rec x2)))
  | (SmtType.Set x1) => (native_and (native_inhabited_type x1) (__smtx_type_wf_rec x1))
  | (SmtType.Seq x1) => (native_and (native_inhabited_type x1) (__smtx_type_wf_rec x1))
  | U => true


def __smtx_type_wf_component (T : SmtType) : native_Bool :=
  (native_and (native_inhabited_type T) (__smtx_type_wf_rec T))

def __smtx_type_wf : SmtType -> native_Bool
  | SmtType.RegLan => true
  | (SmtType.FunType T U) => (native_and (__smtx_type_wf_component T) (__smtx_type_wf U))
  | T => (__smtx_type_wf_component T)


def __smtx_typeof_guard (T : SmtType) (U : SmtType) : SmtType :=
  (native_ite (native_Teq T SmtType.None) SmtType.None U)

def __smtx_typeof_guard_wf (T : SmtType) (U : SmtType) : SmtType :=
  (native_ite (__smtx_type_wf T) U SmtType.None)

def __smtx_msm_get_default : SmtMap -> SmtValue
  | (SmtMap.cons j e m) => (__smtx_msm_get_default m)
  | (SmtMap.default T e) => e


def __smtx_msm_lookup : SmtMap -> SmtValue -> SmtValue
  | (SmtMap.cons j e m), i => (native_ite (native_veq j i) e (__smtx_msm_lookup m i))
  | (SmtMap.default T e), i => e


def __smtx_typeof_map_value : SmtMap -> SmtType
  | (SmtMap.cons i e m) =>
    let _v0 := (__smtx_typeof_map_value m)
    (native_ite (native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e)) _v0) _v0 SmtType.None)
  | (SmtMap.default T e) => (SmtType.Map T (__smtx_typeof_value e))


def __smtx_map_to_set_type : SmtType -> SmtType
  | (SmtType.Map T SmtType.Bool) => (SmtType.Set T)
  | T => SmtType.None


def __smtx_typeof_seq_value : SmtSeq -> SmtType
  | (SmtSeq.cons v vs) =>
    let _v0 := (__smtx_typeof_seq_value vs)
    (native_ite (native_Teq (SmtType.Seq (__smtx_typeof_value v)) _v0) _v0 SmtType.None)
  | (SmtSeq.empty T) => (SmtType.Seq T)


def __smtx_dtc_num_sels : SmtDatatypeCons -> native_Nat
  | (SmtDatatypeCons.cons U c) => (native_nat_succ (__smtx_dtc_num_sels c))
  | SmtDatatypeCons.unit => native_nat_zero


def __smtx_dt_num_sels : SmtDatatype -> native_Nat -> native_Nat
  | (SmtDatatype.sum c d), native_nat_zero => (__smtx_dtc_num_sels c)
  | (SmtDatatype.sum c d), (native_nat_succ n) => (__smtx_dt_num_sels d n)
  | SmtDatatype.null, n => native_nat_zero


def __smtx_typeof_dt_cons_value_rec (T : SmtType) : SmtDatatype -> native_Nat -> SmtType
  | (SmtDatatype.sum SmtDatatypeCons.unit d), native_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), native_nat_zero => (SmtType.DtcAppType U (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) native_nat_zero))
  | (SmtDatatype.sum c d), (native_nat_succ n) => (__smtx_typeof_dt_cons_value_rec T d n)
  | d, n => SmtType.None


def __smtx_typeof_dt_cons_rec (T : SmtType) : SmtDatatype -> native_Nat -> SmtType
  | (SmtDatatype.sum SmtDatatypeCons.unit d), native_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), native_nat_zero => (SmtType.DtcAppType U (__smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) native_nat_zero))
  | (SmtDatatype.sum c d), (native_nat_succ n) => (__smtx_typeof_dt_cons_rec T d n)
  | d, n => SmtType.None


def __smtx_ret_typeof_sel_rec : SmtDatatype -> native_Nat -> native_Nat -> SmtType
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), native_nat_zero, native_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), native_nat_zero, (native_nat_succ m) => (__smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) native_nat_zero m)
  | (SmtDatatype.sum c d), (native_nat_succ n), m => (__smtx_ret_typeof_sel_rec d n m)
  | d, n, m => SmtType.None


def __smtx_ret_typeof_sel (s : native_String) (dd : SmtDatatypeDecl) (n : native_Nat) (m : native_Nat) : SmtType :=
  (__smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) n m)

def __smtx_typeof_apply_value : SmtType -> SmtType -> SmtType
  | (SmtType.DtcAppType T U), V => (__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None))
  | T, U => SmtType.None


def __smtx_typeof_value : SmtValue -> SmtType
  | (SmtValue.Boolean b) => SmtType.Bool
  | (SmtValue.Numeral n) => SmtType.Int
  | (SmtValue.Rational q) => SmtType.Real
  | (SmtValue.Binary w n) => (native_ite (native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w)))) (SmtType.BitVec (native_int_to_nat w)) SmtType.None)
  | (SmtValue.RegLan r) => SmtType.RegLan
  | (SmtValue.Map m) => (__smtx_typeof_map_value m)
  | (SmtValue.Set m) => (__smtx_map_to_set_type (__smtx_typeof_map_value m))
  | (SmtValue.Fun i T U) => (SmtType.FunType T U)
  | (SmtValue.Seq ss) => (__smtx_typeof_seq_value ss)
  | (SmtValue.Char c) => (native_ite (native_char_valid c) SmtType.Char SmtType.None)
  | (SmtValue.UValue i e) => (SmtType.USort i)
  | (SmtValue.DtCons s dd i) => (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dd) (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i)
  | (SmtValue.Apply f v) => (__smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v))
  | v => SmtType.None


def __smtx_model_eval_apply (M : SmtModel) : SmtValue -> SmtValue -> SmtValue
  | v, SmtValue.NotValue => SmtValue.NotValue
  | (SmtValue.DtCons s dd n), i => (SmtValue.Apply (SmtValue.DtCons s dd n) i)
  | (SmtValue.Apply f v), i => (SmtValue.Apply (SmtValue.Apply f v) i)
  | (SmtValue.Fun s T U), i => (native_eval_fun_apply M s T U i)
  | v, i => SmtValue.NotValue


def __smtx_model_eval_dt_sel (M : SmtModel) (s : native_String) (dd : SmtDatatypeDecl) (n : native_Nat) (m : native_Nat) (v : SmtValue) : SmtValue :=
  (native_ite (native_veq (__vsm_apply_head v) (SmtValue.DtCons s dd n)) (__vsm_apply_arg_nth v m (__smtx_dt_num_sels (__smtx_dd_lookup s dd) n)) (__smtx_model_eval_apply M (native_model_lookup M (native_wrong_apply_sel_id n m) (SmtType.FunType (SmtType.Datatype s dd) (__smtx_ret_typeof_sel s dd n m))) v))

def __smtx_model_eval_dt_tester (s : native_String) (dd : SmtDatatypeDecl) (n : native_Nat) (v1 : SmtValue) : SmtValue :=
  (SmtValue.Boolean (native_veq (__vsm_apply_head v1) (SmtValue.DtCons s dd n)))

def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x) => (SmtValue.Boolean (native_not x))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x), (SmtValue.Boolean y) => (SmtValue.Boolean (native_and x y))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_or : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x), (SmtValue.Boolean y) => (SmtValue.Boolean (native_or x y))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_imp (x : SmtValue) (y : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_not x) y)

def __smtx_model_eval_eq : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan r1), (SmtValue.RegLan r2) => (SmtValue.Boolean (native_re_ext_eq r1 r2))
  | v1, v2 => (SmtValue.Boolean (native_veq v1 v2))


def __smtx_model_eval_ite : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean true), x, y => x
  | (SmtValue.Boolean false), x, y => y
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_typeof_apply : SmtType -> SmtType -> SmtType
  | (SmtType.FunType T U), V => (__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None))
  | (SmtType.DtcAppType T U), V => (__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None))
  | T, U => SmtType.None


def __smtx_typeof_eq (T : SmtType) (U : SmtType) : SmtType :=
  (__smtx_typeof_guard T (native_ite (native_Teq T U) SmtType.Bool SmtType.None))

def __smtx_typeof_ite : SmtType -> SmtType -> SmtType -> SmtType
  | SmtType.Bool, U, V => (native_ite (native_Teq U V) U SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof : SmtTerm -> SmtType
  | (SmtTerm.Boolean b) => SmtType.Bool
  | (SmtTerm.Numeral n) => SmtType.Int
  | (SmtTerm.Rational r) => SmtType.Real
  | (SmtTerm.String s) => (native_ite (native_string_valid s) (SmtType.Seq SmtType.Char) SmtType.None)
  | (SmtTerm.Binary w n) => (native_ite (native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w)))) (SmtType.BitVec (native_int_to_nat w)) SmtType.None)
  | (SmtTerm.not x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None)
  | (SmtTerm.and x1 x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.or x1 x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.imp x1 x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.eq x1 x2) => (__smtx_typeof_eq (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.ite x1 x2 x3) => (__smtx_typeof_ite (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.exists s T x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None)
  | (SmtTerm.forall s T x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None)
  | (SmtTerm.choice s T x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (__smtx_typeof_guard_wf T T) SmtType.None)
  | (SmtTerm.bind s T x1 x2) => (native_ite (native_Teq (__smtx_typeof x1) T) (__smtx_typeof_guard_wf T (__smtx_typeof x2)) SmtType.None)
  | (SmtTerm.DtCons s dd i) =>
    let _v0 := (SmtType.Datatype s dd)
    (__smtx_typeof_guard_wf _v0 (__smtx_typeof_dt_cons_rec _v0 (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i))
  | (SmtTerm.Apply (SmtTerm.DtSel s dd i j) x1) =>
    let _v0 := (__smtx_ret_typeof_sel s dd i j)
    (__smtx_typeof_guard_wf _v0 (__smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s dd) _v0) (__smtx_typeof x1)))
  | (SmtTerm.Apply (SmtTerm.DtTester s dd i) x1) =>
    let _v0 := (SmtType.Datatype s dd)
    (__smtx_typeof_guard (__smtx_typeof_dt_cons_rec _v0 (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i) (__smtx_typeof_apply (SmtType.FunType _v0 SmtType.Bool) (__smtx_typeof x1)))
  | (SmtTerm.Apply f x1) => (__smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x1))
  | (SmtTerm.Var s T) => (__smtx_typeof_guard_wf T T)
  | (SmtTerm.UConst s T) => (__smtx_typeof_guard_wf T T)
  | x1 => SmtType.None


def __smtx_is_finite_type (T : SmtType) : native_Bool :=
  (__smtx_type_bounded false T)

def __smtx_field_type_bounded (u : native_Bool) : SmtType -> SmtDatatypeDecl -> native_Bool
  | (SmtType.TypeRef s), ddB => (__smtx_dd_has_dt s ddB)
  | T, ddB => (__smtx_type_bounded u T)
termination_by T ddB => (sizeOf T, 1)


def __smtx_datatype_cons_bounded (u : native_Bool) : SmtDatatypeCons -> SmtDatatypeDecl -> native_Bool
  | SmtDatatypeCons.unit, ddB => true
  | (SmtDatatypeCons.cons T c), ddB => (native_and (__smtx_field_type_bounded u T ddB) (__smtx_datatype_cons_bounded u c ddB))
termination_by c ddB => (sizeOf c, 0)


def __smtx_datatype_bounded (u : native_Bool) : SmtDatatype -> SmtDatatypeDecl -> native_Bool
  | (SmtDatatype.sum c SmtDatatype.null), ddB => (__smtx_datatype_cons_bounded u c ddB)
  | (SmtDatatype.sum c dF), ddB => (native_and (native_not u) (native_and (__smtx_datatype_cons_bounded u c ddB) (__smtx_datatype_bounded u dF ddB)))
  | dF, ddB => (native_not u)
termination_by dF ddB => (sizeOf dF, 0)


def __smtx_datatype_decl_bounded_step (u : native_Bool) : SmtDatatypeDecl -> SmtDatatypeDecl -> SmtDatatypeDecl
  | (SmtDatatypeDecl.cons sF dF ddR), ddB => (__smtx_datatype_decl_bounded_step u ddR (native_ite (native_and (native_not (__smtx_dd_has_dt sF ddB)) (__smtx_datatype_bounded u dF ddB)) (SmtDatatypeDecl.cons sF dF ddB) ddB))
  | SmtDatatypeDecl.nil, ddB => ddB
termination_by ddR ddB => (sizeOf ddR, 0)


def __smtx_datatype_decl_bounded (u : native_Bool) : SmtDatatypeDecl -> SmtDatatypeDecl -> SmtDatatypeDecl -> SmtDatatypeDecl
  | (SmtDatatypeDecl.cons sC dC ddC), dd, ddB => (__smtx_datatype_decl_bounded u ddC dd (__smtx_datatype_decl_bounded_step u dd ddB))
  | SmtDatatypeDecl.nil, dd, ddB => ddB
termination_by ddC dd ddB => (sizeOf dd, sizeOf ddC)


def __smtx_type_bounded (u : native_Bool) : SmtType -> native_Bool
  | (SmtType.Datatype s dd) => (__smtx_dd_has_dt s (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil))
  | SmtType.Bool => (native_not u)
  | (SmtType.BitVec n1) => (native_or (native_not u) (native_nateq n1 native_nat_zero))
  | (SmtType.Map x1 x2) => (native_or (__smtx_type_bounded true x2) (native_and (native_not u) (native_and (__smtx_type_bounded u x1) (__smtx_type_bounded u x2))))
  | (SmtType.Set x1) => (native_and (native_not u) (__smtx_type_bounded u x1))
  | SmtType.Char => (native_not u)
  | T => false
termination_by T => (sizeOf T, 0)


def __smtx_field_type_default (dd : SmtDatatypeDecl) : SmtType -> SmtDatatypeDecl -> SmtValue
  | (SmtType.TypeRef s), ddF => (__smtx_datatype_decl_default s dd ddF)
  | T, ddF => (__smtx_type_default T)
termination_by T ddF => 2 * (sizeOf T + sizeOf ddF) + 3
decreasing_by
  all_goals simp_wf
  all_goals omega


def __smtx_datatype_cons_default (v : SmtValue) (dd : SmtDatatypeDecl) : SmtDatatypeCons -> SmtDatatypeDecl -> SmtValue
  | SmtDatatypeCons.unit, ddF => v
  | (SmtDatatypeCons.cons T c), ddF =>
    let _v0 := (__smtx_field_type_default dd T ddF)
    (native_ite (native_veq _v0 SmtValue.NotValue) SmtValue.NotValue (__smtx_datatype_cons_default (SmtValue.Apply v _v0) dd c ddF))
termination_by c ddF => 2 * (sizeOf c + sizeOf ddF) + 2


def __smtx_datatype_default (s : native_String) (dd : SmtDatatypeDecl) (n : native_Nat) : SmtDatatype -> SmtDatatypeDecl -> SmtValue
  | (SmtDatatype.sum cF dF), ddF =>
    let _v0 := (__smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd cF ddF)
    (native_ite (native_not (native_veq _v0 SmtValue.NotValue)) _v0 (__smtx_datatype_default s dd (native_nat_succ n) dF ddF))
  | dF, ddF => SmtValue.NotValue
termination_by dF ddF => 2 * (sizeOf dF + sizeOf ddF) + 1


def __smtx_datatype_decl_default (s : native_String) (dd : SmtDatatypeDecl) : SmtDatatypeDecl -> SmtValue
  | (SmtDatatypeDecl.cons sF dF ddF) => (native_ite (native_streq s sF) (__smtx_datatype_default s dd native_nat_zero dF ddF) (__smtx_datatype_decl_default s dd ddF))
  | ddF => SmtValue.NotValue
termination_by ddF => 2 * sizeOf ddF


def __smtx_type_default : SmtType -> SmtValue
  | (SmtType.Datatype s dd) => (__smtx_datatype_decl_default s dd dd)
  | SmtType.Bool => (SmtValue.Boolean false)
  | SmtType.Int => (SmtValue.Numeral 0)
  | SmtType.Real => (SmtValue.Rational (native_mk_rational 0 1))
  | SmtType.RegLan => (SmtValue.RegLan native_re_none)
  | (SmtType.BitVec n1) => (SmtValue.Binary (native_nat_to_int n1) 0)
  | (SmtType.Map x1 x2) =>
    let _v0 := (__smtx_type_default x2)
    (native_ite (native_veq _v0 SmtValue.NotValue) SmtValue.NotValue (SmtValue.Map (SmtMap.default x1 _v0)))
  | (SmtType.Set x1) => (SmtValue.Set (SmtMap.default x1 (SmtValue.Boolean false)))
  | (SmtType.Seq x1) => (SmtValue.Seq (SmtSeq.empty x1))
  | SmtType.Char => (SmtValue.Char native_nat_zero)
  | (SmtType.USort i) => (SmtValue.UValue i native_nat_zero)
  | (SmtType.FunType T U) => (SmtValue.Fun native_default_fun_id T U)
  | T => SmtValue.NotValue
termination_by T => 2 * sizeOf T


def __smtx_map_entries_ordered_after (i : SmtValue) : SmtMap -> native_Bool
  | (SmtMap.cons j e m) => (native_vcmp j i)
  | m => true


def __smtx_map_default_canonical (T : SmtType) (e : SmtValue) : native_Bool :=
  (native_ite (__smtx_is_finite_type T) (native_veq e (__smtx_type_default (__smtx_typeof_value e))) true)

def __smtx_map_canonical : SmtMap -> native_Bool
  | (SmtMap.default T e) => (native_and (__smtx_map_default_canonical T e) (__smtx_value_canonical_bool e))
  | (SmtMap.cons i e m) => (native_and (native_and (native_and (native_and (__smtx_value_canonical_bool i) (__smtx_value_canonical_bool e)) (__smtx_map_canonical m)) (__smtx_map_entries_ordered_after i m)) (native_not (native_veq e (__smtx_msm_get_default m))))


def __smtx_seq_canonical : SmtSeq -> native_Bool
  | (SmtSeq.empty T) => true
  | (SmtSeq.cons v s) => (native_and (__smtx_value_canonical_bool v) (__smtx_seq_canonical s))


def __smtx_value_canonical_bool : SmtValue -> native_Bool
  | (SmtValue.Binary w n) => (native_ite (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w))) true)
  | (SmtValue.Char c) => (native_char_valid c)
  | (SmtValue.Map m) => (__smtx_map_canonical m)
  | (SmtValue.Set m) => (native_and (__smtx_map_canonical m) (native_veq (__smtx_msm_get_default m) (SmtValue.Boolean false)))
  | (SmtValue.Seq s) => (__smtx_seq_canonical s)
  | (SmtValue.RegLan r) => (native_re_canonical r)
  | (SmtValue.Apply f v) => (native_and (__smtx_value_canonical_bool f) (__smtx_value_canonical_bool v))
  | v => true




def native_eval_fun_apply (M : SmtModel) (fid : native_String) (T U : SmtType) (i : SmtValue) : SmtValue :=
  let fallback := __smtx_type_default U
  if fid = native_default_fun_id then
    fallback
  else
    native_model_fun_lookup M fid T U i

def native_pack_seq (T : SmtType) : List SmtValue -> SmtSeq
  | [] => (SmtSeq.empty T)
  | v :: vs => (SmtSeq.cons v (native_pack_seq T vs))

def native_pack_string (s : native_String) : SmtSeq :=
  native_pack_seq SmtType.Char (s.map SmtValue.Char)


end

end

noncomputable def __smtx_model_eval (M : SmtModel) : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Rational r) => (SmtValue.Rational r)
  | (SmtTerm.String s) => (SmtValue.Seq (native_pack_string s))
  | (SmtTerm.Binary w n) => (SmtValue.Binary w n)
  | (SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval M x1))
  | (SmtTerm.and x1 x2) => (__smtx_model_eval_and (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.or x1 x2) => (__smtx_model_eval_or (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.imp x1 x2) => (__smtx_model_eval_imp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.eq x1 x2) => (__smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.ite x1 x2 x3) => (__smtx_model_eval_ite (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.exists s T x1) => (native_eval_texists M s T x1)
  | (SmtTerm.forall s T x1) => (native_eval_tforall M s T x1)
  | (SmtTerm.choice s T x1) => (native_eval_tchoice M s T x1)
  | (SmtTerm.bind s T x1 x2) => (__smtx_model_eval (native_model_push M s T (__smtx_model_eval M x1)) x2)
  | (SmtTerm.DtCons s dd i) => (SmtValue.DtCons s dd i)
  | (SmtTerm.Apply (SmtTerm.DtSel s dd i j) x1) => (__smtx_model_eval_dt_sel M s dd i j (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.DtTester s dd i) x1) => (__smtx_model_eval_dt_tester s dd i (__smtx_model_eval M x1))
  | (SmtTerm.Apply f x1) => (__smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x1))
  | (SmtTerm.Var s T) => (native_model_var_lookup M s T)
  | (SmtTerm.UConst s T) => (native_model_lookup M s T)
  | x1 => SmtValue.NotValue
termination_by structural t => t

private theorem __smtx_model_eval_eqns_cache (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  unfold __smtx_model_eval
  rfl




def native_fun_typed (M : SmtModel) : Prop :=
  ∀ fid A B i,
    __smtx_type_wf (SmtType.FunType A B) = true ->
    __smtx_typeof_value i = A ->
    __smtx_typeof_value (native_eval_fun_apply M fid A B i) = B ∧
      __smtx_value_canonical_bool (native_eval_fun_apply M fid A B i) = true

def model_total_typed (M : SmtModel) : Prop :=
  (∀ isVar s T, __smtx_type_wf T = true ->
    __smtx_typeof_value (M.values { isVar := isVar, name := s, ty := T }) = T) ∧
  (∀ isVar s T, __smtx_type_wf T = true ->
    __smtx_value_canonical_bool
      (M.values { isVar := isVar, name := s, ty := T }) = true) ∧
  native_fun_typed M

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_satisfiability : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, model_total_typed M /\ (__smtx_model_eval M t) = (SmtValue.Boolean true)) ->
      smt_satisfiability t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, model_total_typed M -> (__smtx_model_eval M t) = (SmtValue.Boolean false))->
      smt_satisfiability t false

/- ---------------------------------------------- -/

end Smtm
