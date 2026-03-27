import Cpc.SmtEval

set_option linter.unusedVariables false

namespace Smtm

/- SMT literal evaluation defined -/

abbrev smt_lit_Bool := SmtEval.smt_lit_Bool
abbrev smt_lit_Int := SmtEval.smt_lit_Int
abbrev smt_lit_Rat := SmtEval.smt_lit_Rat
abbrev smt_lit_String := SmtEval.smt_lit_String
abbrev smt_lit_Char := Char

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
abbrev smt_lit_RegLan := SmtRegLan

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
abbrev smt_lit_streq := SmtEval.smt_lit_streq

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

abbrev smt_lit_Nat := SmtEval.smt_lit_Nat
abbrev smt_lit_int_to_nat := SmtEval.smt_lit_int_to_nat
abbrev smt_lit_nat_to_int := SmtEval.smt_lit_nat_to_int
abbrev smt_lit_nateq := SmtEval.smt_lit_nateq
  
-- SMT Beyond Eunoia

def smt_lit_int_log2 : smt_lit_Int -> smt_lit_Int
  | x => Int.ofNat (Nat.log2 (Int.toNat x))
  
def smt_lit_str_lt : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | s₁, s₂ => decide (s₁ < s₂)
def smt_lit_str_from_int : smt_lit_Int -> smt_lit_String
  | i => if i < 0 then "" else (toString i)
def smt_lit_str_to_int : smt_lit_String -> smt_lit_Int
  | s => match s.toList with
          | [] => -1
          | '0' :: _ :: _ => -1
          | cs => s.toInt?.getD (-1)
def smt_lit_str_to_upper : smt_lit_String -> smt_lit_String
  | s => s.toUpper
def smt_lit_str_to_lower : smt_lit_String -> smt_lit_String
  | s => s.toLower

-- Regular expressions

def smt_lit_re_nullable : smt_lit_RegLan -> smt_lit_Bool
  | .empty => false
  | .epsilon => true
  | .char _ => false
  | .range _ _ => false
  | .allchar => false
  | .concat r₁ r₂ => smt_lit_re_nullable r₁ && smt_lit_re_nullable r₂
  | .union r₁ r₂ => smt_lit_re_nullable r₁ || smt_lit_re_nullable r₂
  | .inter r₁ r₂ => smt_lit_re_nullable r₁ && smt_lit_re_nullable r₂
  | .star _ => true
  | .comp r => !(smt_lit_re_nullable r)

def smt_lit_re_mk_concat (r₁ r₂ : smt_lit_RegLan) : smt_lit_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r₁, r₂ => .concat r₁ r₂

def smt_lit_re_mk_union (r₁ r₂ : smt_lit_RegLan) : smt_lit_RegLan :=
  match r₁, r₂ with
  | .empty, r => r
  | r, .empty => r
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .union r₁ r₂

def smt_lit_re_mk_inter (r₁ r₂ : smt_lit_RegLan) : smt_lit_RegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .inter r₁ r₂

def smt_lit_re_mk_comp : smt_lit_RegLan -> smt_lit_RegLan
  | .comp r => r
  | r => .comp r

def smt_lit_re_mk_star : smt_lit_RegLan -> smt_lit_RegLan
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

def smt_lit_re_deriv (c : Char) : smt_lit_RegLan -> smt_lit_RegLan
  | .empty => .empty
  | .epsilon => .empty
  | .char d => if c = d then .epsilon else .empty
  | .range lo hi =>
      if lo.toNat <= c.toNat && c.toNat <= hi.toNat then .epsilon else .empty
  | .allchar => .epsilon
  | .concat r₁ r₂ =>
      smt_lit_re_mk_union
        (smt_lit_re_mk_concat (smt_lit_re_deriv c r₁) r₂)
        (if smt_lit_re_nullable r₁ then smt_lit_re_deriv c r₂ else .empty)
  | .union r₁ r₂ => smt_lit_re_mk_union (smt_lit_re_deriv c r₁) (smt_lit_re_deriv c r₂)
  | .inter r₁ r₂ => smt_lit_re_mk_inter (smt_lit_re_deriv c r₁) (smt_lit_re_deriv c r₂)
  | .star r => smt_lit_re_mk_concat (smt_lit_re_deriv c r) (.star r)
  | .comp r => smt_lit_re_mk_comp (smt_lit_re_deriv c r)

def smt_lit_re_of_list : List Char -> smt_lit_RegLan
  | [] => .epsilon
  | c :: cs => smt_lit_re_mk_concat (.char c) (smt_lit_re_of_list cs)

def smt_lit_re_prefix_match_len? (r : smt_lit_RegLan) (xs : List Char) : Option Nat :=
  let rec go (cur : smt_lit_RegLan) (rest : List Char) (n : Nat) : Option Nat :=
    if smt_lit_re_nullable cur then
      some n
    else
      match rest with
      | [] => none
      | c :: cs => go (smt_lit_re_deriv c cur) cs (n + 1)
  go r xs 0

def smt_lit_re_find_idx_aux (r : smt_lit_RegLan) (xs : List Char) (idx : Nat) : Option (Nat × Nat) :=
  match smt_lit_re_prefix_match_len? r xs with
  | some n => some (idx, n)
  | none =>
      match xs with
      | [] => none
      | _ :: cs => smt_lit_re_find_idx_aux r cs (idx + 1)

def smt_lit_re_find_idx_from (r : smt_lit_RegLan) (xs : List Char) (start : Nat) : Option (Nat × Nat) :=
  smt_lit_re_find_idx_aux r (xs.drop start) start

def smt_lit_re_replace_all_list_aux (fuel : Nat) (r : smt_lit_RegLan) (replacement : List Char) :
    List Char -> List Char
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match smt_lit_re_prefix_match_len? r xs with
          | some 0 =>
              match xs with
              | [] => replacement
              | c :: cs => replacement ++ (c :: smt_lit_re_replace_all_list_aux fuel r replacement cs)
          | some (n + 1) =>
              replacement ++ smt_lit_re_replace_all_list_aux fuel r replacement (xs.drop (n + 1))
          | none =>
              match xs with
              | [] => []
              | c :: cs => c :: smt_lit_re_replace_all_list_aux fuel r replacement cs

def smt_lit_re_replace_all_list (r : smt_lit_RegLan) (replacement xs : List Char) : List Char :=
  smt_lit_re_replace_all_list_aux (xs.length + 1) r replacement xs

def smt_lit_str_to_re : smt_lit_String -> smt_lit_RegLan
  | s => smt_lit_re_of_list s.toList
def smt_lit_re_mult : smt_lit_RegLan -> smt_lit_RegLan
  | r => smt_lit_re_mk_star r
def smt_lit_re_plus : smt_lit_RegLan -> smt_lit_RegLan
  | r => smt_lit_re_mk_concat r (smt_lit_re_mk_star r)
def smt_lit_re_comp : smt_lit_RegLan -> smt_lit_RegLan
  | r => smt_lit_re_mk_comp r
def smt_lit_re_concat : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | r₁, r₂ => smt_lit_re_mk_concat r₁ r₂
def smt_lit_re_inter : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | r₁, r₂ => smt_lit_re_mk_inter r₁ r₂
def smt_lit_re_diff : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | r₁, r₂ => smt_lit_re_mk_inter r₁ (smt_lit_re_mk_comp r₂)
def smt_lit_re_union : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | r₁, r₂ => smt_lit_re_mk_union r₁ r₂
def smt_lit_re_range : smt_lit_String -> smt_lit_String -> smt_lit_RegLan
  | s₁, s₂ =>
      match s₁.toList, s₂.toList with
      | [c₁], [c₂] => .range c₁ c₂
      | _, _ => .empty
def smt_lit_str_in_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Bool
  | s, r =>
      smt_lit_re_nullable <| s.toList.foldl (fun acc c => smt_lit_re_deriv c acc) r
def smt_lit_str_indexof_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Int -> smt_lit_Int
  | s, r, i =>
      if i < 0 then
        -1
      else
        match smt_lit_re_find_idx_from r s.toList (Int.toNat i) with
        | some (idx, _) => Int.ofNat idx
        | none => -1
def smt_lit_str_replace_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | s, r, replacement =>
      match smt_lit_re_find_idx_from r s.toList 0 with
      | some (idx, len) =>
          String.ofList <| (s.toList.take idx) ++ replacement.toList ++ (s.toList.drop (idx + len))
      | none => s
def smt_lit_str_replace_re_all : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | s, r, replacement => String.ofList <| smt_lit_re_replace_all_list r replacement.toList s.toList
def smt_lit_re_allchar : smt_lit_RegLan := .allchar
def smt_lit_re_none : smt_lit_RegLan := .empty
def smt_lit_re_all : smt_lit_RegLan := .star .allchar

-- Partial semantics

def smt_lit_qdiv_by_zero_id : smt_lit_String := "@qdiv_by_zero"
def smt_lit_div_by_zero_id : smt_lit_String := "@div_by_zero"
def smt_lit_mod_by_zero_id : smt_lit_String := "@mod_by_zero"
def smt_lit_wrong_apply_sel_id : smt_lit_String := "@wrong_apply_sel"
def smt_lit_oob_seq_nth_id : smt_lit_String := "@oob_seq_nth"
def smt_lit_uconst_id : smt_lit_Nat -> smt_lit_String
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
  name : smt_lit_String
  ty : SmtType
deriving Repr, DecidableEq, Inhabited

abbrev SmtModel := SmtModelKey -> Option SmtValue

def SmtModel.empty : SmtModel :=
  fun _ => none

def __smtx_model_key (s : smt_lit_String) (T : SmtType) : SmtModelKey :=
  { name := s, ty := T }

def __smtx_model_lookup (M : SmtModel) (s : smt_lit_String) (T : SmtType) : SmtValue :=
  match M (__smtx_model_key s T) with
  | some v => v
  | none => SmtValue.NotValue

def __smtx_model_push (M : SmtModel) (s : smt_lit_String) (T : SmtType) (v : SmtValue) : SmtModel :=
  fun k =>
    if k = (__smtx_model_key s T) then
      some v
    else
      M k

/- Type equality -/
def smt_lit_Teq : SmtType -> SmtType -> smt_lit_Bool
  | x, y => decide (x = y)
/- Value equality -/
def smt_lit_veq : SmtValue -> SmtValue -> smt_lit_Bool
  | x, y => decide (x = y)

macro_rules
  | `(smt_lit_veq_ext $m1 $m2) => do
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
  | `(smt_lit_eval_texists $M $s $T $body) => do
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
  | `(smt_lit_eval_tforall $M $s $T $body) => do
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
  | `(smt_lit_eval_tchoice $M $s $T $body) => do
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

def smt_lit_inhabited_type (T : SmtType) : smt_lit_Bool := by
  classical
  exact decide (∃ v : SmtValue, __smtx_typeof_value v = T)

$LEAN_SMT_EVAL_DEFS$

def smt_lit_unpack_seq : SmtSeq -> List SmtValue
  | (SmtSeq.cons v vs) => v :: (smt_lit_unpack_seq vs)
  | (SmtSeq.empty _) => []


def smt_lit_pack_seq (T : SmtType) : List SmtValue -> SmtSeq
  | [] => (SmtSeq.empty T)
  | v :: vs => (SmtSeq.cons v (smt_lit_pack_seq T vs))


def __smtx_ssm_char_values_of_string (s : smt_lit_String) : List SmtValue :=
  s.toList.map SmtValue.Char

def __smtx_ssm_char_of_value : SmtValue -> Char
  | (SmtValue.Char c) => c
  | _ => Char.ofNat 0

def __smtx_ssm_string_of_char_values (xs : List SmtValue) : smt_lit_String :=
  String.ofList (xs.map __smtx_ssm_char_of_value)

def smt_lit_unpack_string (x : SmtSeq) : smt_lit_String :=
  (__smtx_ssm_string_of_char_values (smt_lit_unpack_seq x))

def smt_lit_pack_string (s : smt_lit_String) : SmtSeq :=
  (smt_lit_pack_seq SmtType.Char (__smtx_ssm_char_values_of_string s))

  
def __smtx_value_eqb (v1 : SmtValue) (v2 : SmtValue) : smt_lit_Bool :=
  match __smtx_model_eval_eq v1 v2 with
  | (SmtValue.Boolean b) => b
  | _ => false


def smt_lit_seq_prefix_eq : List SmtValue -> List SmtValue -> smt_lit_Bool
  | [], _ => true
  | _ :: _, [] => false
  | v1 :: vs1, v2 :: vs2 => (__smtx_value_eqb v1 v2) && (smt_lit_seq_prefix_eq vs1 vs2)


def smt_lit_seq_len : List SmtValue -> smt_lit_Int
  | x => Int.ofNat x.length

def smt_lit_seq_concat : List SmtValue -> List SmtValue -> List SmtValue
  | x, y => x ++ y
  
def smt_lit_seq_extract (xs : List SmtValue) (i : smt_lit_Int) (n : smt_lit_Int) : List SmtValue :=
  let len : smt_lit_Int := Int.ofNat xs.length
  if i < 0 || n <= 0 || i >= len then
    []
  else
    let start : Nat := Int.toNat i
    let take : Nat := Int.toNat (min n (len - i))
    (xs.drop start).take take


def smt_lit_seq_indexof_rec (xs pat : List SmtValue) (i fuel : Nat) : smt_lit_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if smt_lit_seq_prefix_eq pat xs then
        Int.ofNat i
      else
        match xs with
        | [] => -1
        | _ :: ys => (smt_lit_seq_indexof_rec ys pat (i + 1) fuel)


def smt_lit_seq_indexof (xs pat : List SmtValue) (i : smt_lit_Int) : smt_lit_Int :=
  if i < 0 then
    -1
  else
    let start := Int.toNat i
    let patLen := pat.length
    let xsLen := xs.length
    if h : start + patLen <= xsLen then
      (smt_lit_seq_indexof_rec (xs.drop start) pat start (xsLen - (start + patLen) + 1))
    else
      -1


def smt_lit_seq_replace (xs pat repl : List SmtValue) : List SmtValue :=
  match pat with
  | [] => repl ++ xs
  | _ =>
      let idx := smt_lit_seq_indexof xs pat 0
      if idx < 0 then
        xs
      else
        let n := Int.toNat idx
        (xs.take n) ++ repl ++ (xs.drop (n + pat.length))


def smt_lit_seq_replace_all_aux (fuel : Nat) (pat repl : List SmtValue) :
    List SmtValue -> List SmtValue
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match pat with
          | [] => xs
          | _ =>
              let idx := smt_lit_seq_indexof xs pat 0
              if idx < 0 then
                xs
              else
                let n := Int.toNat idx
                (xs.take n) ++ repl ++
                  (smt_lit_seq_replace_all_aux fuel pat repl (xs.drop (n + pat.length)))


def smt_lit_seq_replace_all (xs pat repl : List SmtValue) : List SmtValue :=
  (smt_lit_seq_replace_all_aux (xs.length + 1) pat repl xs)


def smt_lit_seq_update (xs : List SmtValue) (i : smt_lit_Int) (ys : List SmtValue) : List SmtValue :=
  let len : smt_lit_Int := Int.ofNat xs.length
  if i < 0 || len <= i then
    xs
  else
    let idx := Int.toNat i
    (xs.take idx) ++ ys ++ (xs.drop (idx + 1))
    
def smt_lit_seq_rev : List SmtValue -> List SmtValue
  | xs => xs.reverse
  
def smt_lit_seq_contains (xs pat : List SmtValue) : smt_lit_Bool :=
  (0 <= (smt_lit_seq_indexof xs pat 0))

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

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_satisfiability : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, (smt_interprets M t true)) ->
      smt_satisfiability t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, ¬ (smt_interprets M t true))->
      smt_satisfiability t false

/- ---------------------------------------------- -/

end Smtm
