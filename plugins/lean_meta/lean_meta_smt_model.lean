module

public import $EO_CALC$.SmtEval
import all $EO_CALC$.SmtEval

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

/- SMT literal evaluation defined -/

-- Note: the type of regular languages (native_RegLan) carries SmtValue as
-- base elements and is hence declared in the mutual block of SMT datatypes
-- below. All regular expression operations are defined after that block.

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

mutual

/-
SMT-LIB types.
-/
inductive SmtType : Type where
$LEAN_SMT_TYPE_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
$LEAN_SMT_TERM_DEF$
deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB values.
-/
inductive SmtValue : Type where
$LEAN_SMT_VALUE_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/-
Regular languages. Base elements are SmtValue, which allows regular
expression operations to be defined uniformly over the same (unpacked)
sequence representation used by the sequence operations. Well-formed
regular languages carry only valid character values as base elements
(see native_re_canonical and native_re_elem_valid below).
-/
inductive native_RegLan : Type where
  | empty : native_RegLan
  | epsilon : native_RegLan
  | char : SmtValue -> native_RegLan
  | range : SmtValue -> SmtValue -> native_RegLan
  | allchar : native_RegLan
  | concat : native_RegLan -> native_RegLan -> native_RegLan
  | union : native_RegLan -> native_RegLan -> native_RegLan
  | inter : native_RegLan -> native_RegLan -> native_RegLan
  | star : native_RegLan -> native_RegLan
  | comp : native_RegLan -> native_RegLan
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB map values.
-/
inductive SmtMap : Type where
  | cons : SmtValue -> SmtValue -> SmtMap -> SmtMap
  | default : SmtType -> SmtValue -> SmtMap
deriving Repr, DecidableEq, Inhabited, Ord

/- 
SMT-LIB sequence values.
-/
inductive SmtSeq : Type where
  | cons : SmtValue -> SmtSeq -> SmtSeq
  | empty : SmtType -> SmtSeq
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB datatype declarations.
-/
inductive SmtDatatypeDecl : Type where
  | nil : SmtDatatypeDecl
  | cons : native_String -> SmtDatatype -> SmtDatatypeDecl -> SmtDatatypeDecl
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB datatypes.
-/
inductive SmtDatatype : Type where
  | null : SmtDatatype
  | sum : SmtDatatypeCons -> SmtDatatype -> SmtDatatype
deriving Repr, DecidableEq, Inhabited, Ord

/-
SMT-LIB datatype constructors.
-/
inductive SmtDatatypeCons : Type where
  | unit : SmtDatatypeCons
  | cons : SmtType -> SmtDatatypeCons -> SmtDatatypeCons
deriving Repr, DecidableEq, Inhabited, Ord

end

abbrev SmtNativeFun := SmtValue -> SmtValue

def native_default_ifun_id : native_String := (native_string_lit "@native_default_ifun")

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
  match compare v1 v2 with
  | Ordering.lt => true
  | _ => false

-- Regular expressions

abbrev SmtRegLan := native_RegLan

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

def native_re_nullable : native_RegLan -> native_Bool
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

def native_re_concat (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r₁, r₂ => .concat r₁ r₂

def native_re_union (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, r => r
  | r, .empty => r
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .union r₁ r₂

def native_re_inter (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .inter r₁ r₂

def native_re_comp : native_RegLan -> native_RegLan
  | .comp r => r
  | r => .comp r

def native_re_mult : native_RegLan -> native_RegLan
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

def native_re_deriv (c : SmtValue) : native_RegLan -> native_RegLan
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

def native_re_of_list : List SmtValue -> native_RegLan
  | [] => .epsilon
  | c :: cs => native_re_concat (.char c) (native_re_of_list cs)

def native_re_prefix_match_len?.go (r : native_RegLan) :
    List SmtValue → Nat → Option Nat
  | [], n =>
      if native_re_nullable r then some n else none
  | c :: cs, n =>
      if native_re_nullable r then
        some n
      else
        native_re_prefix_match_len?.go (native_re_deriv c r) cs (n + 1)

def native_re_prefix_match_len? (r : native_RegLan)
    (xs : List SmtValue) : Option Nat :=
  native_re_prefix_match_len?.go r xs 0

def native_re_positive_prefix_match_len? (r : native_RegLan) :
    List SmtValue -> Option Nat
  | [] => none
  | c :: cs =>
      match native_re_prefix_match_len? (native_re_deriv c r) cs with
      | some n => some (n + 1)
      | none => none

def native_re_find_idx_aux (r : native_RegLan) (xs : List SmtValue) (idx : Nat) : Option (Nat × Nat) :=
  match native_re_prefix_match_len? r xs with
  | some n => some (idx, n)
  | none =>
      match xs with
      | [] => none
      | _ :: cs => native_re_find_idx_aux r cs (idx + 1)

def native_re_find_idx_from (r : native_RegLan) (xs : List SmtValue) (start : Nat) : Option (Nat × Nat) :=
  native_re_find_idx_aux r (xs.drop start) start

def native_re_find_nonempty_idx_aux (r : native_RegLan) (xs : List SmtValue) (idx : Nat) :
    Option (Nat × Nat) :=
  match native_re_positive_prefix_match_len? r xs with
  | some (n + 1) => some (idx, n + 1)
  | _ =>
      match xs with
      | [] => none
      | _ :: cs => native_re_find_nonempty_idx_aux r cs (idx + 1)

def native_re_find_nonempty_idx_from (r : native_RegLan) (xs : List SmtValue) (start : Nat) :
    Option (Nat × Nat) :=
  native_re_find_nonempty_idx_aux r (xs.drop start) start

def native_re_replace_all_nonempty_list_aux (fuel : Nat) (r : native_RegLan)
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

def native_re_replace_all_nonempty_list (r : native_RegLan) (replacement xs : List SmtValue) :
    List SmtValue :=
  native_re_replace_all_nonempty_list_aux (xs.length + 1) r replacement xs

def native_str_to_re : List SmtValue -> native_RegLan
  | s => native_re_of_list s
def native_re_diff : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_inter r₁ (native_re_comp r₂)
def native_re_range : List SmtValue -> List SmtValue -> native_RegLan
  | s₁, s₂ =>
      match s₁, s₂ with
      | [v₁], [v₂] => .range v₁ v₂
      | _, _ => .empty
def native_str_in_re : List SmtValue -> native_RegLan -> native_Bool
  | s, r =>
      if native_re_str_valid s then
        native_re_nullable <| s.foldl (fun acc c => native_re_deriv c acc) r
      else
        false
def native_str_indexof_re : List SmtValue -> native_RegLan -> native_Int -> native_Int
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
def native_str_indexof_re_split_aux (r1 r2 : native_RegLan) :
    List SmtValue -> List SmtValue -> native_Nat -> native_Int
  | pre, suf, i =>
      if native_str_in_re pre r1 && native_str_in_re suf r2 then
        Int.ofNat i
      else
        match suf with
        | [] => -1
        | c :: cs => native_str_indexof_re_split_aux r1 r2 (pre ++ [c]) cs (i + 1)
def native_str_indexof_re_split : List SmtValue -> native_RegLan -> native_RegLan -> native_Int
  | s, r1, r2 =>
      if native_re_str_valid s then
        native_str_indexof_re_split_aux r1 r2 [] s 0
      else
        -1
def native_str_replace_re : List SmtValue -> native_RegLan -> List SmtValue -> List SmtValue
  | s, r, replacement =>
      match native_re_find_idx_from r s 0 with
      | some (idx, len) =>
          (s.take idx) ++ replacement ++ (s.drop (idx + len))
      | none => s
def native_str_replace_re_all : List SmtValue -> native_RegLan -> List SmtValue -> List SmtValue
  | s, r, replacement =>
      native_re_replace_all_nonempty_list r replacement s
/-- End positions of the nonempty-match scan used by `str.replace_re_all`:
successive leftmost, shortest, nonempty matches of `r` in `s` at or after
`pos`.  Each step consumes at least one character, so `s.length + 1` fuel is
always sufficient. -/
def native_re_scan_ends_aux (fuel : Nat) (r : native_RegLan) (s : List SmtValue) :
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
def native_str_occur_index_re (s : List SmtValue) (r : native_RegLan) (n : native_Int) : native_Int :=
  let bnds := 0 :: native_re_scan_ends_aux (s.length + 1) r s 0
  if 0 ≤ n ∧ Int.toNat n < bnds.length then
    Int.ofNat (bnds.getD (Int.toNat n) 0)
  else
    -1

def native_re_allchar : native_RegLan := .allchar
def native_re_none : native_RegLan := .empty
def native_re_all : native_RegLan := .star .allchar

def native_re_canonical : native_RegLan -> native_Bool
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


$LEAN_SMT_EVAL_DEFS$

def native_eval_ifun_apply (M : SmtModel) (fid : native_String) (T U : SmtType) (i : SmtValue) : SmtValue :=
  let fallback := __smtx_type_default U
  if fid = native_default_ifun_id then
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

$LEAN_SMT_EVAL$

def native_fun_typed (M : SmtModel) : Prop :=
  ∀ fid A B i,
    __smtx_type_wf (SmtType.FunType A B) = true ->
    __smtx_typeof_value i = A ->
    __smtx_typeof_value (native_eval_ifun_apply M fid A B i) = B ∧
      __smtx_value_canonical_bool (native_eval_ifun_apply M fid A B i) = true

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
