import Cpc.SmtEval

set_option linter.unusedVariables false

namespace Smtm

/- SMT literal evaluation defined -/

abbrev smt_lit_Bool := SmtEval.smt_lit_Bool
abbrev smt_lit_Int := SmtEval.smt_lit_Int
abbrev smt_lit_Rat := SmtEval.smt_lit_Rat
abbrev smt_lit_String := SmtEval.smt_lit_String

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
def smt_lit_str_update : smt_lit_String -> smt_lit_Int -> smt_lit_String -> smt_lit_String
  | s, i, t =>
      if i < 0 || smt_lit_str_len s <= i then
        s
      else
        let idx := Int.toNat i
        String.ofList <| s.toList.take idx ++ t.toList ++ s.toList.drop (idx + 1)
def smt_lit_str_rev : smt_lit_String -> smt_lit_String
  | s => String.ofList s.toList.reverse
def smt_lit_str_replace_first (s pat repl : smt_lit_String) : smt_lit_String :=
  if pat = "" then
    repl ++ s
  else
    let idx := smt_lit_str_indexof s pat 0
    if idx < 0 then
      s
    else
      let n := Int.toNat idx
      String.ofList <| s.toList.take n ++ repl.toList ++ s.toList.drop (n + pat.length)
def smt_lit_str_replace : smt_lit_String -> smt_lit_String -> smt_lit_String -> smt_lit_String
  | s, t1, t2 => smt_lit_str_replace_first s t1 t2
def smt_lit_str_replace_all : smt_lit_String -> smt_lit_String -> smt_lit_String -> smt_lit_String
  | s, t1, t2 => s.replace t1 t2
def smt_lit_str_contains : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | s, t => s.contains t

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

def smt_lit_qdiv_by_zero_id : smt_lit_Int := -1
def smt_lit_div_by_zero_id : smt_lit_Int := -2
def smt_lit_mod_by_zero_id : smt_lit_Int := -3
def smt_lit_wrong_apply_sel_id : smt_lit_Int := -4

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
  | USort : smt_lit_Nat -> SmtType

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
  | ite : SmtTerm
  | eq : SmtTerm
  | exists : smt_lit_String -> SmtType -> SmtTerm
  | forall : smt_lit_String -> SmtType -> SmtTerm
  | lambda : smt_lit_String -> SmtType -> SmtTerm
  | choice : smt_lit_String -> SmtType -> SmtTerm
  | DtCons : smt_lit_String -> SmtDatatype -> smt_lit_Nat -> SmtTerm
  | DtSel : smt_lit_String -> SmtDatatype -> smt_lit_Nat -> smt_lit_Nat -> SmtTerm
  | DtTester : smt_lit_String -> SmtDatatype -> smt_lit_Nat -> SmtTerm
  | Const : SmtValue -> SmtType -> SmtTerm
  | UConst : smt_lit_Nat -> SmtType -> SmtTerm
  | not : SmtTerm
  | and : SmtTerm

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
  | DtCons : smt_lit_String -> SmtDatatype -> smt_lit_Nat -> SmtValue
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
abbrev SmtModel := Int

-- FIXME:
-- (__smtx_model_lookup M n T) should return an arbitrary SMT value whose type
-- is T.
def __smtx_model_lookup : SmtModel -> smt_lit_Int -> SmtType -> SmtValue
  | _, _, _ => (SmtValue.Boolean true)


/- Type equality -/
def smt_lit_Teq : SmtType -> SmtType -> smt_lit_Bool
  | x, y => decide (x = y)
/- Value equality -/
def smt_lit_veq : SmtValue -> SmtValue -> smt_lit_Bool
  | x, y => decide (x = y)
  
/- exists -/
def smt_lit_tforall : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME
/- forall -/
def smt_lit_texists : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME
/- choice -/
def smt_lit_tchoice : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _, _ => (SmtValue.Boolean true) -- FIXME
/- extentional equality for values -/
def smt_lit_veq_ext : SmtValue -> SmtValue -> SmtValue
  | _, _ => (SmtValue.Boolean true) -- FIXME

/- Definition of SMT-LIB model semantics -/

mutual

def __vsm_apply_head : SmtValue -> SmtValue
  | (SmtValue.Apply f a) => (__vsm_apply_head f)
  | a => a


def __vsm_apply_arg_nth : SmtValue -> smt_lit_Nat -> SmtValue
  | (SmtValue.Apply f a), smt_lit_nat_zero => a
  | (SmtValue.Apply f a), (smt_lit_nat_succ n) => (__vsm_apply_arg_nth f n)
  | a, n => SmtValue.NotValue


def __smtx_msm_lookup : SmtMap -> SmtValue -> SmtValue
  | (SmtMap.cons j e m), i => (smt_lit_ite (smt_lit_veq j i) e (__smtx_msm_lookup m i))
  | (SmtMap.default T e), i => e


def __smtx_typeof_map_value : SmtMap -> SmtType
  | (SmtMap.cons i e m) => (smt_lit_ite (smt_lit_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e)) (__smtx_typeof_map_value m)) (__smtx_typeof_map_value m) SmtType.None)
  | (SmtMap.default T e) => (SmtType.Map T (__smtx_typeof_value e))


def __smtx_index_typeof_map : SmtType -> SmtType
  | (SmtType.Map T U) => T
  | T => SmtType.None


def __smtx_typeof_seq_value : SmtSeq -> SmtType
  | (SmtSeq.cons v vs) => (smt_lit_ite (smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)) (__smtx_typeof_seq_value vs) SmtType.None)
  | (SmtSeq.empty T) => (SmtType.Seq T)


def __smtx_dtc_substitute (s : smt_lit_String) (d : SmtDatatype) : SmtDatatypeCons -> SmtDatatypeCons
  | (SmtDatatypeCons.cons (SmtType.Datatype s2 d2) c) => (SmtDatatypeCons.cons (SmtType.Datatype s2 (smt_lit_ite (smt_lit_streq s s2) d2 (__smtx_dt_substitute s d d2))) (__smtx_dtc_substitute s d c))
  | (SmtDatatypeCons.cons T c) => (SmtDatatypeCons.cons (smt_lit_ite (smt_lit_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T) (__smtx_dtc_substitute s d c))
  | SmtDatatypeCons.unit => SmtDatatypeCons.unit


def __smtx_dt_substitute (s : smt_lit_String) (d : SmtDatatype) : SmtDatatype -> SmtDatatype
  | (SmtDatatype.sum c d2) => (SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d d2))
  | SmtDatatype.null => SmtDatatype.null


def __smtx_typeof_dt_cons_value_rec (T : SmtType) : SmtDatatype -> smt_lit_Nat -> SmtType
  | SmtDatatype.null, smt_lit_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons U c) d), smt_lit_nat_zero => (SmtType.DtConsType U (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) smt_lit_nat_zero))
  | (SmtDatatype.sum c d), (smt_lit_nat_succ n) => (__smtx_typeof_dt_cons_value_rec T d n)
  | d, n => SmtType.None


def __smtx_ret_typeof_sel : SmtDatatype -> smt_lit_Nat -> smt_lit_Nat -> SmtType
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), smt_lit_nat_zero, smt_lit_nat_zero => T
  | (SmtDatatype.sum (SmtDatatypeCons.cons T c) d), smt_lit_nat_zero, (smt_lit_nat_succ m) => (__smtx_ret_typeof_sel (SmtDatatype.sum c d) smt_lit_nat_zero m)
  | (SmtDatatype.sum c d), (smt_lit_nat_succ n), m => (__smtx_ret_typeof_sel d n m)
  | d, n, m => SmtType.None


def __smtx_typeof_apply_value : SmtType -> SmtType -> SmtType
  | (SmtType.DtConsType T U), V => (smt_lit_ite (smt_lit_Teq T V) U SmtType.None)
  | T, U => SmtType.None


def __smtx_typeof_value : SmtValue -> SmtType
  | (SmtValue.Boolean b) => SmtType.Bool
  | (SmtValue.Numeral n) => SmtType.Int
  | (SmtValue.Rational q) => SmtType.Real
  | (SmtValue.String s) => (SmtType.Seq SmtType.Char)
  | (SmtValue.Binary w n) => (smt_lit_ite (smt_lit_zleq 0 w) (SmtType.BitVec w) SmtType.None)
  | (SmtValue.RegLan r) => SmtType.RegLan
  | (SmtValue.Map m) => (__smtx_typeof_map_value m)
  | (SmtValue.Seq ss) => (__smtx_typeof_seq_value ss)
  | (SmtValue.DtCons s d i) => (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i)
  | (SmtValue.Apply f v) => (__smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v))
  | v => SmtType.None


def __smtx_model_eval_ite : SmtValue -> SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean true), t2, t3 => t2
  | (SmtValue.Boolean false), t2, t3 => t3
  | t1, t2, t3 => SmtValue.NotValue


def __smtx_model_eval_eq : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m1), (SmtValue.Map m2) => (smt_lit_veq_ext (SmtValue.Map m1) (SmtValue.Map m2))
  | t1, t2 => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) (__smtx_typeof_value t2)) (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) SmtType.None) SmtValue.NotValue (SmtValue.Boolean (smt_lit_veq t1 t2))) SmtValue.NotValue)


def __smtx_map_select : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Map m), i => (smt_lit_ite (smt_lit_Teq (__smtx_index_typeof_map (__smtx_typeof_map_value m)) (__smtx_typeof_value i)) (__smtx_msm_lookup m i) SmtValue.NotValue)
  | v, i => SmtValue.NotValue


def __smtx_model_eval_dt_cons (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Nat) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n) SmtType.None) SmtValue.NotValue (SmtValue.DtCons s d n))

def __smtx_model_eval_dt_sel (M : SmtModel) (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Nat) (m : smt_lit_Nat) (v : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v) (SmtType.Datatype s d)) (smt_lit_ite (smt_lit_veq (__vsm_apply_head v) (SmtValue.DtCons s d n)) (__vsm_apply_arg_nth v m) (__smtx_map_select (__smtx_map_select (__smtx_map_select (__smtx_model_lookup M smt_lit_wrong_apply_sel_id (SmtType.Map SmtType.Int (SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel d n m))))) (SmtValue.Numeral (smt_lit_nat_to_int n))) (SmtValue.Numeral (smt_lit_nat_to_int m))) v)) SmtValue.NotValue)

def __smtx_model_eval_dt_tester (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Nat) (v1 : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v1) (SmtType.Datatype s d)) (SmtValue.Boolean (smt_lit_veq (__vsm_apply_head v1) (SmtValue.DtCons s d n))) SmtValue.NotValue)

def __smtx_model_eval_apply : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Apply f v), i => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value (SmtValue.Apply (SmtValue.Apply f v) i)) SmtType.None) SmtValue.NotValue (SmtValue.Apply (SmtValue.Apply f v) i))
  | (SmtValue.Map m), i => (__smtx_map_select (SmtValue.Map m) i)
  | v, i => SmtValue.NotValue


def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (smt_lit_not x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_and x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval (M : SmtModel) : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Rational r) => (SmtValue.Rational r)
  | (SmtTerm.String s) => (SmtValue.String s)
  | (SmtTerm.Binary w n) => (smt_lit_ite (smt_lit_and (smt_lit_zleq 0 w) (smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)))) (SmtValue.Binary w n) SmtValue.NotValue)
  | (SmtTerm.Apply SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x1) x2) => (__smtx_model_eval_and (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite x1) x2) x3) => (__smtx_model_eval_ite (__smtx_model_eval M x1) (__smtx_model_eval M x2) (__smtx_model_eval M x3))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) => (__smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.exists s T) x1) => (smt_lit_tforall M s T x1)
  | (SmtTerm.Apply (SmtTerm.forall s T) x1) => (smt_lit_texists M s T x1)
  | (SmtTerm.Apply (SmtTerm.lambda s T) x1) => (SmtValue.Lambda s T x1)
  | (SmtTerm.Apply (SmtTerm.choice s T) x1) => (smt_lit_tchoice M s T x1)
  | (SmtTerm.DtCons s d i) => (__smtx_model_eval_dt_cons s d i)
  | (SmtTerm.Apply (SmtTerm.DtSel s d i j) x1) => (__smtx_model_eval_dt_sel M s d i j (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.DtTester s d i) x1) => (__smtx_model_eval_dt_tester s d i (__smtx_model_eval M x1))
  | (SmtTerm.Apply f x1) => (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x1))
  | (SmtTerm.Const v T) => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v) T) v SmtValue.NotValue)
  | (SmtTerm.UConst i T) => (__smtx_model_lookup M (smt_lit_nat_to_int i) T)
  | x1 => SmtValue.NotValue




end

inductive smt_model_interprets : SmtModel -> SmtTerm -> Bool -> Prop
  | intro_true  (M : SmtModel) (t : SmtTerm) :
      (__smtx_model_eval M t) = (SmtValue.Boolean true) ->
      (smt_model_interprets M t true)
  | intro_false (M : SmtModel) (t : SmtTerm) :
      (__smtx_model_eval M t) = (SmtValue.Boolean false)->
      smt_model_interprets M t false

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_interprets : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, (smt_model_interprets M t true)) ->
      smt_interprets t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, (smt_model_interprets M t false))->
      smt_interprets t false

/- FIXME inductive smt_model_well_typed : SmtModel -> Prop, based on smt axiom -/

/- ---------------------------------------------- -/

end Smtm
