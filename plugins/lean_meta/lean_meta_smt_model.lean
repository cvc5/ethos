import $EO_CALC$.SmtEval

set_option linter.unusedVariables false

namespace Smtm

open SmtEval

/- SMT literal evaluation defined -/

abbrev native_Char := Char

inductive SmtRegLan : Type where
  | empty : SmtRegLan
  | epsilon : SmtRegLan
  | char : Char -> SmtRegLan
  | range : Char -> Char -> SmtRegLan
  | allchar : SmtRegLan
  | concat : SmtRegLan -> SmtRegLan -> SmtRegLan
  | union : SmtRegLan -> SmtRegLan -> SmtRegLan
  | inter : SmtRegLan -> SmtRegLan -> SmtRegLan
  | star : SmtRegLan -> SmtRegLan
  | comp : SmtRegLan -> SmtRegLan
deriving Repr, DecidableEq, Inhabited
abbrev native_RegLan := SmtRegLan
  
-- SMT Beyond Eunoia

def native_int_log2 : native_Int -> native_Int
  | x => Int.ofNat (Nat.log2 (Int.toNat x))
  
def native_str_lt : native_String -> native_String -> native_Bool
  | s₁, s₂ => decide (s₁ < s₂)
def native_str_from_int : native_Int -> native_String
  | i => if i < 0 then "" else (toString i)
def native_str_to_int : native_String -> native_Int
  | s => match s.toList with
          | [] => -1
          | '0' :: _ :: _ => -1
          | cs => s.toInt?.getD (-1)
def native_str_to_upper : native_String -> native_String
  | s => s.toUpper
def native_str_to_lower : native_String -> native_String
  | s => s.toLower

-- Regular expressions

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

def native_re_mk_concat (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r₁, r₂ => .concat r₁ r₂

def native_re_mk_union (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, r => r
  | r, .empty => r
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .union r₁ r₂

def native_re_mk_inter (r₁ r₂ : native_RegLan) : native_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .inter r₁ r₂

def native_re_mk_comp : native_RegLan -> native_RegLan
  | .comp r => r
  | r => .comp r

def native_re_mk_star : native_RegLan -> native_RegLan
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

def native_re_deriv (c : Char) : native_RegLan -> native_RegLan
  | .empty => .empty
  | .epsilon => .empty
  | .char d => if c = d then .epsilon else .empty
  | .range lo hi =>
      if lo.toNat <= c.toNat && c.toNat <= hi.toNat then .epsilon else .empty
  | .allchar => .epsilon
  | .concat r₁ r₂ =>
      native_re_mk_union
        (native_re_mk_concat (native_re_deriv c r₁) r₂)
        (if native_re_nullable r₁ then native_re_deriv c r₂ else .empty)
  | .union r₁ r₂ => native_re_mk_union (native_re_deriv c r₁) (native_re_deriv c r₂)
  | .inter r₁ r₂ => native_re_mk_inter (native_re_deriv c r₁) (native_re_deriv c r₂)
  | .star r => native_re_mk_concat (native_re_deriv c r) (.star r)
  | .comp r => native_re_mk_comp (native_re_deriv c r)

def native_re_of_list : List Char -> native_RegLan
  | [] => .epsilon
  | c :: cs => native_re_mk_concat (.char c) (native_re_of_list cs)

def native_re_prefix_match_len? (r : native_RegLan) (xs : List Char) : Option Nat :=
  let rec go (cur : native_RegLan) (rest : List Char) (n : Nat) : Option Nat :=
    if native_re_nullable cur then
      some n
    else
      match rest with
      | [] => none
      | c :: cs => go (native_re_deriv c cur) cs (n + 1)
  go r xs 0

def native_re_find_idx_aux (r : native_RegLan) (xs : List Char) (idx : Nat) : Option (Nat × Nat) :=
  match native_re_prefix_match_len? r xs with
  | some n => some (idx, n)
  | none =>
      match xs with
      | [] => none
      | _ :: cs => native_re_find_idx_aux r cs (idx + 1)

def native_re_find_idx_from (r : native_RegLan) (xs : List Char) (start : Nat) : Option (Nat × Nat) :=
  native_re_find_idx_aux r (xs.drop start) start

def native_re_replace_all_list_aux (fuel : Nat) (r : native_RegLan) (replacement : List Char) :
    List Char -> List Char
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match native_re_prefix_match_len? r xs with
          | some 0 =>
              match xs with
              | [] => replacement
              | c :: cs => replacement ++ (c :: native_re_replace_all_list_aux fuel r replacement cs)
          | some (n + 1) =>
              replacement ++ native_re_replace_all_list_aux fuel r replacement (xs.drop (n + 1))
          | none =>
              match xs with
              | [] => []
              | c :: cs => c :: native_re_replace_all_list_aux fuel r replacement cs

def native_re_replace_all_list (r : native_RegLan) (replacement xs : List Char) : List Char :=
  native_re_replace_all_list_aux (xs.length + 1) r replacement xs

def native_str_to_re : native_String -> native_RegLan
  | s => native_re_of_list s.toList
def native_re_mult : native_RegLan -> native_RegLan
  | r => native_re_mk_star r
def native_re_plus : native_RegLan -> native_RegLan
  | r => native_re_mk_concat r (native_re_mk_star r)
def native_re_comp : native_RegLan -> native_RegLan
  | r => native_re_mk_comp r
def native_re_concat : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_mk_concat r₁ r₂
def native_re_inter : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_mk_inter r₁ r₂
def native_re_diff : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_mk_inter r₁ (native_re_mk_comp r₂)
def native_re_union : native_RegLan -> native_RegLan -> native_RegLan
  | r₁, r₂ => native_re_mk_union r₁ r₂
def native_re_range : native_String -> native_String -> native_RegLan
  | s₁, s₂ =>
      match s₁.toList, s₂.toList with
      | [c₁], [c₂] => .range c₁ c₂
      | _, _ => .empty
def native_str_in_re : native_String -> native_RegLan -> native_Bool
  | s, r =>
      native_re_nullable <| s.toList.foldl (fun acc c => native_re_deriv c acc) r
def native_str_indexof_re : native_String -> native_RegLan -> native_Int -> native_Int
  | s, r, i =>
      if i < 0 then
        -1
      else
        match native_re_find_idx_from r s.toList (Int.toNat i) with
        | some (idx, _) => Int.ofNat idx
        | none => -1
def native_str_replace_re : native_String -> native_RegLan -> native_String -> native_String
  | s, r, replacement =>
      match native_re_find_idx_from r s.toList 0 with
      | some (idx, len) =>
          String.ofList <| (s.toList.take idx) ++ replacement.toList ++ (s.toList.drop (idx + len))
      | none => s
def native_str_replace_re_all : native_String -> native_RegLan -> native_String -> native_String
  | s, r, replacement => String.ofList <| native_re_replace_all_list r replacement.toList s.toList
def native_re_allchar : native_RegLan := .allchar
def native_re_none : native_RegLan := .empty
def native_re_all : native_RegLan := .star .allchar

-- Partial semantics

def native_qdiv_by_zero_id : native_String := "@qdiv_by_zero"
def native_div_by_zero_id : native_String := "@div_by_zero"
def native_mod_by_zero_id : native_String := "@mod_by_zero"
def native_wrong_apply_sel_id : native_String := "@wrong_apply_sel"
def native_oob_seq_nth_id : native_String := "@oob_seq_nth"
def native_uconst_id : native_Nat -> native_String
  | i => "@u." ++ toString i

mutual

/- 
SMT-LIB types.
-/
inductive SmtType : Type where
$LEAN_SMT_TYPE_DEF$
deriving Repr, DecidableEq, Inhabited

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


/- SMT-LIB model -/
structure SmtModelKey where
  name : native_String
  ty : SmtType
deriving Repr, DecidableEq, Inhabited

abbrev SmtModel := SmtModelKey -> Option SmtValue

def SmtModel.empty : SmtModel :=
  fun _ => none

def __smtx_model_key (s : native_String) (T : SmtType) : SmtModelKey :=
  { name := s, ty := T }

def __smtx_model_lookup (M : SmtModel) (s : native_String) (T : SmtType) : SmtValue :=
  match M (__smtx_model_key s T) with
  | some v => v
  | none => SmtValue.NotValue

def __smtx_model_push (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) : SmtModel :=
  fun k =>
    if k = (__smtx_model_key s T) then
      some v
    else
      M k

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

macro_rules
  | `(native_veq_ext $m1 $m2) => do
      let lookupId := Lean.mkIdent `__smtx_msm_lookup
      `(by
          classical
          exact
            if hExt :
                ∀ v : SmtValue,
                  $lookupId $m1 v = $lookupId $m2 v then
              true
            else
              false)
  | `(native_eval_texists $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `__smtx_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      `(by
          classical
          exact
            if h :
                ∃ v : SmtValue,
                  $typeofValueId v = $T ∧
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              SmtValue.Boolean true
            else
              SmtValue.Boolean false)
  | `(native_eval_tforall $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `__smtx_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      `(by
          classical
          exact
            if h :
                ∀ v : SmtValue,
                  $typeofValueId v = $T ->
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              SmtValue.Boolean true
            else
              SmtValue.Boolean false)
  | `(native_eval_tchoice $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `__smtx_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      `(by
          classical
          exact
            if hSat :
                ∃ v : SmtValue,
                  $typeofValueId v = $T ∧
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              Classical.choose hSat
            else if hTy : ∃ v : SmtValue, $typeofValueId v = $T then
              Classical.choose hTy
            else
              SmtValue.NotValue)

/- Definition of SMT-LIB model semantics -/

noncomputable section

mutual

def native_inhabited_type (T : SmtType) : native_Bool := by
  classical
  exact decide (∃ v : SmtValue, __smtx_typeof_value v = T)

$LEAN_SMT_EVAL_DEFS$

def native_unpack_seq : SmtSeq -> List SmtValue
  | (SmtSeq.cons v vs) => v :: (native_unpack_seq vs)
  | (SmtSeq.empty _) => []


def native_pack_seq (T : SmtType) : List SmtValue -> SmtSeq
  | [] => (SmtSeq.empty T)
  | v :: vs => (SmtSeq.cons v (native_pack_seq T vs))


def __smtx_ssm_char_values_of_string (s : native_String) : List SmtValue :=
  s.toList.map SmtValue.Char

def __smtx_ssm_char_of_value : SmtValue -> Char
  | (SmtValue.Char c) => c
  | _ => Char.ofNat 0

def __smtx_ssm_string_of_char_values (xs : List SmtValue) : native_String :=
  String.ofList (xs.map __smtx_ssm_char_of_value)

def native_unpack_string (x : SmtSeq) : native_String :=
  (__smtx_ssm_string_of_char_values (native_unpack_seq x))

def native_pack_string (s : native_String) : SmtSeq :=
  (native_pack_seq SmtType.Char (__smtx_ssm_char_values_of_string s))

  
def __smtx_value_eqb (v1 : SmtValue) (v2 : SmtValue) : native_Bool :=
  match __smtx_model_eval_eq v1 v2 with
  | (SmtValue.Boolean b) => b
  | _ => false


def native_seq_prefix_eq : List SmtValue -> List SmtValue -> native_Bool
  | [], _ => true
  | _ :: _, [] => false
  | v1 :: vs1, v2 :: vs2 => (__smtx_value_eqb v1 v2) && (native_seq_prefix_eq vs1 vs2)


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


def native_seq_indexof_rec (xs pat : List SmtValue) (i fuel : Nat) : native_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if native_seq_prefix_eq pat xs then
        Int.ofNat i
      else
        match xs with
        | [] => -1
        | _ :: ys => (native_seq_indexof_rec ys pat (i + 1) fuel)


def native_seq_indexof (xs pat : List SmtValue) (i : native_Int) : native_Int :=
  if i < 0 then
    -1
  else
    let start := Int.toNat i
    let patLen := pat.length
    let xsLen := xs.length
    if h : start + patLen <= xsLen then
      (native_seq_indexof_rec (xs.drop start) pat start (xsLen - (start + patLen) + 1))
    else
      -1


def native_seq_replace (xs pat repl : List SmtValue) : List SmtValue :=
  match pat with
  | [] => repl ++ xs
  | _ =>
      let idx := native_seq_indexof xs pat 0
      if idx < 0 then
        xs
      else
        let n := Int.toNat idx
        (xs.take n) ++ repl ++ (xs.drop (n + pat.length))


def native_seq_replace_all_aux (fuel : Nat) (pat repl : List SmtValue) :
    List SmtValue -> List SmtValue
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match pat with
          | [] => xs
          | _ =>
              let idx := native_seq_indexof xs pat 0
              if idx < 0 then
                xs
              else
                let n := Int.toNat idx
                (xs.take n) ++ repl ++
                  (native_seq_replace_all_aux fuel pat repl (xs.drop (n + pat.length)))


def native_seq_replace_all (xs pat repl : List SmtValue) : List SmtValue :=
  (native_seq_replace_all_aux (xs.length + 1) pat repl xs)


def native_seq_update (xs : List SmtValue) (i : native_Int) (ys : List SmtValue) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || len <= i then
    xs
  else
    let idx := Int.toNat i
    (xs.take idx) ++ ys ++ (xs.drop (idx + 1))
    
def native_seq_rev : List SmtValue -> List SmtValue
  | xs => xs.reverse
  
def native_seq_contains (xs pat : List SmtValue) : native_Bool :=
  (0 <= (native_seq_indexof xs pat 0))

end

end

$LEAN_SMT_EVAL$

inductive smt_interprets : SmtModel -> SmtTerm -> Bool -> Prop
  | intro_true  (M : SmtModel) (t : SmtTerm) :
      (__smtx_typeof t) = SmtType.Bool ->
      (__smtx_model_eval M t) = (SmtValue.Boolean true) ->
      (smt_interprets M t true)
  | intro_false (M : SmtModel) (t : SmtTerm) :
      (__smtx_typeof t) = SmtType.Bool ->
      (__smtx_model_eval M t) = (SmtValue.Boolean false)->
      smt_interprets M t false

def type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

def model_total_typed (M : SmtModel) : Prop :=
  (∀ s T, type_inhabited T -> __smtx_typeof_value (__smtx_model_lookup M s T) = T) ∧
  (∀ s T, ¬ type_inhabited T -> __smtx_model_lookup M s T = SmtValue.NotValue)

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_satisfiability : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, model_total_typed M /\ (smt_interprets M t true)) ->
      smt_satisfiability t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, model_total_typed M -> ¬ (smt_interprets M t true))->
      smt_satisfiability t false

/- ---------------------------------------------- -/

end Smtm
