module

public import Cpc.SmtValueOrder
import all Cpc.SmtValueOrder

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval


abbrev SmtNativeFun := SmtValue -> SmtValue

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

abbrev RefList := List native_String

def native_reflist_nil : RefList := []
def native_reflist_insert (xs : RefList) (s : native_String) := (s :: xs)
def native_reflist_contains (xs : RefList) (s : native_String ) :=
  decide (s ∈ xs)

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

def native_int_log2 : native_Int -> native_Int
  | x => Int.ofNat (Nat.log2 (Int.toNat x))
def native_zabs : native_Int -> native_Int
  | x => if x < 0 then -x else x
def native_qabs : native_Rat -> native_Rat
  | x => if x < 0 then -x else x
  
def native_char_is_digit (c : native_Char) : native_Bool :=
  48 <= c && c <= 57

def native_char_to_upper (c : native_Char) : native_Char :=
  if 97 <= c && c <= 122 then c - 32 else c

def native_char_to_lower (c : native_Char) : native_Char :=
  if 65 <= c && c <= 90 then c + 32 else c

def native_decimal_digits_to_nat (xs : native_String) : native_Nat :=
  xs.foldl (fun acc c => 10 * acc + (c - 48)) 0

def native_str_lt : native_String -> native_String -> native_Bool
  | s₁, s₂ => decide (s₁ < s₂)
def native_str_from_int : native_Int -> native_String
  | i => if i < 0 then native_string_lit "" else native_string_lit (toString i)
def native_str_to_int : native_String -> native_Int
  | s => match s with
          | [] => -1
          | _ => if s.all native_char_is_digit then Int.ofNat (native_decimal_digits_to_nat s) else -1
def native_str_to_upper : native_String -> native_String
  | s => s.map native_char_to_upper
def native_str_to_lower : native_String -> native_String
  | s => s.map native_char_to_lower

-- Partial semantics

def native_qdiv_by_zero_id : native_String := (native_string_lit "@qdiv_by_zero")
def native_div_by_zero_id : native_String := (native_string_lit "@div_by_zero")
def native_mod_by_zero_id : native_String := (native_string_lit "@mod_by_zero")
def native_wrong_apply_sel_id (n m : native_Nat) : native_String :=
  (native_string_lit "@wrong_apply_sel_") ++ (native_string_lit (toString n)) ++ (native_string_lit "_") ++ (native_string_lit (toString m))
def native_oob_seq_nth_id : native_String := (native_string_lit "@oob_seq_nth")
def native_uconst_id : native_Nat -> native_String
  | i => (native_string_lit "@u.") ++ (native_string_lit (toString i))
def native_const_id : native_Nat -> native_String
  | i => (native_string_lit "@c.") ++ (native_string_lit (toString i))

-- Regular expressions

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

def native_re_mult : SmtRegLan -> SmtRegLan
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

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

def native_re_of_list : List SmtValue -> SmtRegLan
  | [] => .epsilon
  | c :: cs => native_re_concat (.char c) (native_re_of_list cs)

def native_re_prefix_match_len?.go (r : SmtRegLan) :
    List SmtValue → Nat → Option Nat
  | [], n =>
      if native_re_nullable r then some n else none
  | c :: cs, n =>
      if native_re_nullable r then
        some n
      else
        native_re_prefix_match_len?.go (native_re_deriv c r) cs (n + 1)

def native_re_prefix_match_len? (r : SmtRegLan)
    (xs : List SmtValue) : Option Nat :=
  native_re_prefix_match_len?.go r xs 0

def native_re_positive_prefix_match_len? (r : SmtRegLan) :
    List SmtValue -> Option Nat
  | [] => none
  | c :: cs =>
      match native_re_prefix_match_len? (native_re_deriv c r) cs with
      | some n => some (n + 1)
      | none => none

def native_re_find_idx_aux (r : SmtRegLan) (xs : List SmtValue) (idx : Nat) : Option (Nat × Nat) :=
  match native_re_prefix_match_len? r xs with
  | some n => some (idx, n)
  | none =>
      match xs with
      | [] => none
      | _ :: cs => native_re_find_idx_aux r cs (idx + 1)

def native_re_find_idx_from (r : SmtRegLan) (xs : List SmtValue) (start : Nat) : Option (Nat × Nat) :=
  native_re_find_idx_aux r (xs.drop start) start

def native_re_find_nonempty_idx_aux (r : SmtRegLan) (xs : List SmtValue) (idx : Nat) :
    Option (Nat × Nat) :=
  match native_re_positive_prefix_match_len? r xs with
  | some (n + 1) => some (idx, n + 1)
  | _ =>
      match xs with
      | [] => none
      | _ :: cs => native_re_find_nonempty_idx_aux r cs (idx + 1)

def native_re_find_nonempty_idx_from (r : SmtRegLan) (xs : List SmtValue) (start : Nat) :
    Option (Nat × Nat) :=
  native_re_find_nonempty_idx_aux r (xs.drop start) start

def native_re_replace_all_nonempty_list_aux (fuel : Nat) (r : SmtRegLan)
    (replacement : List SmtValue) : List SmtValue -> List SmtValue
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match native_re_positive_prefix_match_len? r xs with
          | some (n + 1) =>
              replacement ++ native_re_replace_all_nonempty_list_aux fuel r replacement
                (xs.drop (n + 1))
          | _ =>
              match xs with
              | [] => []
              | c :: cs => c :: native_re_replace_all_nonempty_list_aux fuel r replacement cs

def native_re_replace_all_nonempty_list (r : SmtRegLan) (replacement xs : List SmtValue) :
    List SmtValue :=
  native_re_replace_all_nonempty_list_aux (xs.length + 1) r replacement xs

def native_str_to_re : List SmtValue -> SmtRegLan
  | s => native_re_of_list s
def native_re_diff : SmtRegLan -> SmtRegLan -> SmtRegLan
  | r₁, r₂ => native_re_inter r₁ (native_re_comp r₂)
def native_re_range : List SmtValue -> List SmtValue -> SmtRegLan
  | s₁, s₂ =>
      match s₁, s₂ with
      | [v₁], [v₂] => .range v₁ v₂
      | _, _ => .empty
def native_str_in_re : List SmtValue -> SmtRegLan -> native_Bool
  | s, r =>
      if native_re_str_valid s then
        native_re_nullable <| s.foldl (fun acc c => native_re_deriv c acc) r
      else
        false
def native_str_indexof_re : List SmtValue -> SmtRegLan -> native_Int -> native_Int
  | s, r, i =>
      if i < 0 then
        -1
      else
        let start := Int.toNat i
        if start <= s.length then
          match native_re_find_idx_from r s start with
          | some (idx, _) => Int.ofNat idx
          | none => -1
        else
          -1
/-- Searches for the smallest split point of `s` into a prefix matching `r1` and a
suffix matching `r2`.  `pre` is the prefix consumed so far (i.e. `s` with `suf`
dropped) and `i` its length; recursion is structural on the remaining suffix. -/
def native_str_indexof_re_split_aux (r1 r2 : SmtRegLan) :
    List SmtValue -> List SmtValue -> native_Nat -> native_Int
  | pre, suf, i =>
      if native_str_in_re pre r1 && native_str_in_re suf r2 then
        Int.ofNat i
      else
        match suf with
        | [] => -1
        | c :: cs => native_str_indexof_re_split_aux r1 r2 (pre ++ [c]) cs (i + 1)
def native_str_indexof_re_split : List SmtValue -> SmtRegLan -> SmtRegLan -> native_Int
  | s, r1, r2 =>
      if native_re_str_valid s then
        native_str_indexof_re_split_aux r1 r2 [] s 0
      else
        -1
def native_str_replace_re : List SmtValue -> SmtRegLan -> List SmtValue -> List SmtValue
  | s, r, replacement =>
      match native_re_find_idx_from r s 0 with
      | some (idx, len) =>
          (s.take idx) ++ replacement ++ (s.drop (idx + len))
      | none => s
def native_str_replace_re_all : List SmtValue -> SmtRegLan -> List SmtValue -> List SmtValue
  | s, r, replacement =>
      native_re_replace_all_nonempty_list r replacement s
/-- End positions of the nonempty-match scan used by `str.replace_re_all`:
successive leftmost, shortest, nonempty matches of `r` in `s` at or after
`pos`.  Each step consumes at least one character, so `s.length + 1` fuel is
always sufficient. -/
def native_re_scan_ends_aux (fuel : Nat) (r : SmtRegLan) (s : List SmtValue) :
    Nat -> List Nat
  | pos =>
      match fuel with
      | 0 => []
      | fuel + 1 =>
          match native_re_find_nonempty_idx_from r s pos with
          | some (idx, len) =>
              (idx + len) :: native_re_scan_ends_aux fuel r s (idx + len)
          | none => []

/-- The `n`-th boundary of the nonempty-match scan of `r` over `s`: `0` for
`n = 0`, the end position of the `n`-th match for `1 <= n <=` the number of
matches, and `-1` out of range. The sequence occurrence-index operator is
evaluated by this operator via a singleton regular expression over its
pattern. -/
def native_str_occur_index_re (s : List SmtValue) (r : SmtRegLan) (n : native_Int) : native_Int :=
  let bnds := 0 :: native_re_scan_ends_aux (s.length + 1) r s 0
  if 0 ≤ n ∧ Int.toNat n < bnds.length then
    Int.ofNat (bnds.getD (Int.toNat n) 0)
  else
    -1

def native_re_allchar : SmtRegLan := .allchar
def native_re_none : SmtRegLan := .empty
def native_re_all : SmtRegLan := .star .allchar

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
  | `(native_eval_map_diff_msm $m1 $m2) => do
      let lookupId := Lean.mkIdent `__smtx_msm_lookup
      let typeofMapValueId := Lean.mkIdent `__smtx_typeof_map_value
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      let typeDefaultId := Lean.mkIdent `__smtx_type_default
      let canonId := Lean.mkIdent `__smtx_value_canonical_bool
      `(by
          classical
          exact
            match ($typeofMapValueId $m1, $typeofMapValueId $m2) with
            | (SmtType.Map T1 U1, SmtType.Map T2 U2) =>
                native_ite (native_and (native_Teq T1 T2) (native_Teq U1 U2))
                  (if hDiff :
                      ∃ i : SmtValue,
                        $typeofValueId i = T1 ∧
                          $canonId i = true ∧
                            native_veq ($lookupId $m1 i) ($lookupId $m2 i) = false then
                    Classical.choose hDiff
                  else
                    $typeDefaultId T1)
                  SmtValue.NotValue
            | _ => SmtValue.NotValue)
  | `(native_eval_seq_diff_ssm $s1 $s2) => do
      `(by
          classical
          exact
            -- an arbitrary index at which the two sequences differ: a
            -- position whose elements disagree, where a missing element
            -- past the end of the shorter sequence counts as a
            -- disagreement. Such an index exists exactly when the two
            -- sequences are unequal; when they are equal we return -1.
            (let rec seqNth : SmtSeq -> Nat -> SmtValue
              | SmtSeq.cons v _, 0 => v
              | SmtSeq.cons _ vs, Nat.succ n => seqNth vs n
              | SmtSeq.empty _, _ => SmtValue.NotValue
              if hDiff : ∃ i : Nat, native_not (native_veq (seqNth $s1 i) (seqNth $s2 i)) then
                SmtValue.Numeral (Int.ofNat (Classical.choose hDiff))
              else
                SmtValue.Numeral (-1)))

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
  | (SmtType.Seq x1) => (native_and (native_inhabited_type x1) (__smtx_type_wf_rec x1))
  | (SmtType.Map x1 x2) => (native_and (native_and (native_inhabited_type x1) (__smtx_type_wf_rec x1)) (native_and (native_inhabited_type x2) (__smtx_type_wf_rec x2)))
  | (SmtType.FunType x1 x2) => false
  | (SmtType.Set x1) => (native_and (native_inhabited_type x1) (__smtx_type_wf_rec x1))
  | (SmtType.DtcAppType x1 x2) => false
  | SmtType.None => false
  | SmtType.RegLan => false
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


def __smtx_model_eval_ite : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean true), t2, t3 => t2
  | (SmtValue.Boolean false), t2, t3 => t3
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_eq : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.RegLan r1), (SmtValue.RegLan r2) => (SmtValue.Boolean (native_re_ext_eq r1 r2))
  | v1, v2 => (SmtValue.Boolean (native_veq v1 v2))


def __smtx_model_eval_map_diff : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (native_eval_map_diff_msm m1 m2)
  | (SmtValue.Set m1), (SmtValue.Set m2) => (native_eval_map_diff_msm m1 m2)
  | v1, v2 => SmtValue.NotValue


def __smtx_model_eval_seq_diff : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Seq s1), (SmtValue.Seq s2) => (native_eval_seq_diff_ssm s1 s2)
  | v1, v2 => SmtValue.NotValue


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
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (native_not x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_or : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (native_or x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (native_and x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_imp (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_not x1) x2)

def __smtx_typeof_ite : SmtType -> SmtType -> SmtType -> SmtType
  | SmtType.Bool, U, V => (native_ite (native_Teq U V) U SmtType.None)
  | T, U, V => SmtType.None


def __smtx_typeof_eq (T : SmtType) (U : SmtType) : SmtType :=
  (__smtx_typeof_guard T (native_ite (native_Teq T U) SmtType.Bool SmtType.None))

def __smtx_typeof_apply : SmtType -> SmtType -> SmtType
  | (SmtType.FunType T U), V => (__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None))
  | (SmtType.DtcAppType T U), V => (__smtx_typeof_guard T (native_ite (native_Teq T V) U SmtType.None))
  | T, U => SmtType.None


def __smtx_typeof_map_diff : SmtType -> SmtType -> SmtType
  | (SmtType.Map T1 U1), (SmtType.Map T2 U2) => (native_ite (native_and (native_Teq T1 T2) (native_Teq U1 U2)) T1 SmtType.None)
  | (SmtType.Set T1), (SmtType.Set T2) => (native_ite (native_Teq T1 T2) T1 SmtType.None)
  | T1, T2 => SmtType.None


def __smtx_typeof_seq_diff : SmtType -> SmtType -> SmtType
  | (SmtType.Seq T1), (SmtType.Seq T2) => (native_ite (native_Teq T1 T2) SmtType.Int SmtType.None)
  | T1, T2 => SmtType.None


def __smtx_typeof : SmtTerm -> SmtType
  | (SmtTerm.Boolean b) => SmtType.Bool
  | (SmtTerm.Numeral n) => SmtType.Int
  | (SmtTerm.Rational r) => SmtType.Real
  | (SmtTerm.String s) => (native_ite (native_string_valid s) (SmtType.Seq SmtType.Char) SmtType.None)
  | (SmtTerm.Binary w n) => (native_ite (native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w)))) (SmtType.BitVec (native_int_to_nat w)) SmtType.None)
  | (SmtTerm.not x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) SmtType.Bool SmtType.None)
  | (SmtTerm.or x1 x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.and x1 x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.imp x1 x2) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (native_ite (native_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None)
  | (SmtTerm.ite x1 x2 x3) => (__smtx_typeof_ite (__smtx_typeof x1) (__smtx_typeof x2) (__smtx_typeof x3))
  | (SmtTerm.eq x1 x2) => (__smtx_typeof_eq (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.exists s T x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None)
  | (SmtTerm.forall s T x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None)
  | (SmtTerm.choice s T x1) => (native_ite (native_Teq (__smtx_typeof x1) SmtType.Bool) (__smtx_typeof_guard_wf T T) SmtType.None)
  | (SmtTerm.bind s T x1 x2) => (native_ite (native_Teq (__smtx_typeof x1) T) (__smtx_typeof_guard_wf T (__smtx_typeof x2)) SmtType.None)
  | (SmtTerm.map_diff x1 x2) => (__smtx_typeof_map_diff (__smtx_typeof x1) (__smtx_typeof x2))
  | (SmtTerm.seq_diff x1 x2) => (__smtx_typeof_seq_diff (__smtx_typeof x1) (__smtx_typeof x2))
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
  | SmtType.Bool => (native_not u)
  | (SmtType.BitVec w) => (native_or (native_not u) (native_nateq w native_nat_zero))
  | SmtType.Char => (native_not u)
  | (SmtType.Datatype s dd) => (__smtx_dd_has_dt s (__smtx_datatype_decl_bounded u dd dd SmtDatatypeDecl.nil))
  | (SmtType.Map T U) => (native_or (__smtx_type_bounded true U) (native_and (native_not u) (native_and (__smtx_type_bounded u T) (__smtx_type_bounded u U))))
  | (SmtType.Set T) => (native_and (native_not u) (__smtx_type_bounded u T))
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
  | (SmtType.BitVec w) => (SmtValue.Binary (native_nat_to_int w) 0)
  | SmtType.Char => (SmtValue.Char native_nat_zero)
  | (SmtType.Map T U) => 
    let _v0 := (__smtx_type_default U)
    (native_ite (native_veq _v0 SmtValue.NotValue) SmtValue.NotValue (SmtValue.Map (SmtMap.default T _v0)))
  | (SmtType.Set T) => (SmtValue.Set (SmtMap.default T (SmtValue.Boolean false)))
  | (SmtType.Seq T) => (SmtValue.Seq (SmtSeq.empty T))
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

def native_unpack_seq : SmtSeq -> List SmtValue
  | (SmtSeq.cons v vs) => v :: (native_unpack_seq vs)
  | (SmtSeq.empty _) => []

def native_pack_seq (T : SmtType) : List SmtValue -> SmtSeq
  | [] => (SmtSeq.empty T)
  | v :: vs => (SmtSeq.cons v (native_pack_seq T vs))

def native_ssm_char_of_value : SmtValue -> native_Char
  | (SmtValue.Char c) => c
  | _ => 0

def native_unpack_string (x : SmtSeq) : native_String :=
  (native_unpack_seq x).map native_ssm_char_of_value

def native_pack_string (s : native_String) : SmtSeq :=
  native_pack_seq SmtType.Char (s.map SmtValue.Char)

def native_seq_len : List SmtValue -> native_Int
  | x => Int.ofNat x.length

def native_seq_concat : List SmtValue -> List SmtValue -> List SmtValue
  | x, y => x ++ y
  
def native_seq_extract (xs : List SmtValue) (i : native_Int) (n : native_Int) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || n <= 0 || i >= len then
    []
  else
    let start : Nat := Int.toNat i
    let take : Nat := Int.toNat (min n (len - i))
    (xs.drop start).take take

/-- Generic sequence pattern operations share the regular expression matcher.
These small adapters also give the SMT backend distinct entry points that it
can map directly to the corresponding polymorphic `seq.*` operators. -/
def native_seq_indexof (xs pat : List SmtValue) (i : native_Int) : native_Int :=
  native_str_indexof_re xs (native_str_to_re pat) i

def native_seq_contains (xs pat : List SmtValue) : native_Bool :=
  0 <= native_seq_indexof xs pat 0

def native_seq_replace (xs pat repl : List SmtValue) : List SmtValue :=
  native_str_replace_re xs (native_str_to_re pat) repl

def native_seq_replace_all (xs pat repl : List SmtValue) : List SmtValue :=
  native_str_replace_re_all xs (native_str_to_re pat) repl

def native_seq_occur_index (xs pat : List SmtValue) (n : native_Int) : native_Int :=
  native_str_occur_index_re xs (native_str_to_re pat) n

def native_seq_update (xs : List SmtValue) (i : native_Int) (ys : List SmtValue) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || len <= i then
    xs
  else
    let idx := Int.toNat i
    (xs.take idx) ++ (ys.take (xs.length - idx)) ++
      (xs.drop (idx + ys.length))
    
def native_seq_rev : List SmtValue -> List SmtValue
  | xs => xs.reverse

end

end

noncomputable def __smtx_model_eval (M : SmtModel) : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Rational r) => (SmtValue.Rational r)
  | (SmtTerm.String s) => (SmtValue.Seq (native_pack_string s))
  | (SmtTerm.Binary w n) => (SmtValue.Binary w n)
  | (SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval M x1))
  | (SmtTerm.or x1 x2) => (__smtx_model_eval_or (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.and x1 x2) => (__smtx_model_eval_and (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.imp x1 x2) => (__smtx_model_eval_imp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.ite x1 x2 x3) => (__smtx_model_eval_ite (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.eq x1 x2) => (__smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.exists s T x1) => (native_eval_texists M s T x1)
  | (SmtTerm.forall s T x1) => (native_eval_tforall M s T x1)
  | (SmtTerm.choice s T x1) => (native_eval_tchoice M s T x1)
  | (SmtTerm.bind s T x1 x2) => (__smtx_model_eval (native_model_push M s T (__smtx_model_eval M x1)) x2)
  | (SmtTerm.map_diff x1 x2) => (__smtx_model_eval_map_diff (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.seq_diff x1 x2) => (__smtx_model_eval_seq_diff (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.DtCons s dd i) => (SmtValue.DtCons s dd i)
  | (SmtTerm.Apply (SmtTerm.DtSel s dd i j) x1) => (__smtx_model_eval_dt_sel M s dd i j (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.DtTester s dd i) x1) => (__smtx_model_eval_dt_tester s dd i (__smtx_model_eval M x1))
  | (SmtTerm.Apply f x1) => (__smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x1))
  | (SmtTerm.Var s T) => (native_model_var_lookup M s T)
  | (SmtTerm.UConst s T) => (native_model_lookup M s T)
  | x1 => SmtValue.NotValue
termination_by structural t => t

private theorem __smtx_model_eval_eqns_cache (M : SmtModel) (b : native_Bool) :
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
