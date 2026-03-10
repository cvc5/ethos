set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace SmtEval

abbrev smt_lit_Bool := Bool
abbrev smt_lit_Int := Int
abbrev smt_lit_Rat := Rat
abbrev smt_lit_String := String
abbrev smt_lit_RegLan := String -- FIXME

/- Evaluation functions -/

def smt_lit_ite {T : Type} (c : smt_lit_Bool) (t e : T) : T :=
  if c then t else e
def smt_lit_not : smt_lit_Bool -> smt_lit_Bool
  | x => Bool.not x
def smt_lit_and : smt_lit_Bool -> smt_lit_Bool -> smt_lit_Bool
  | x, y => x && y
def smt_lit_iff : smt_lit_Bool -> smt_lit_Bool -> smt_lit_Bool
  | x, y => decide (x = y)
def smt_lit_or : smt_lit_Bool -> smt_lit_Bool -> smt_lit_Bool
  | x, y => x || y
def smt_lit_xor : smt_lit_Bool -> smt_lit_Bool -> smt_lit_Bool
  | x, y => Bool.xor x y

-- Integer arithmetic
def smt_lit_zplus : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | x, y => x+y
def smt_lit_zmult : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | x, y => x*y
def smt_lit_zneg : smt_lit_Int -> smt_lit_Int
  | x => -x
def smt_lit_zeq : smt_lit_Int -> smt_lit_Int -> smt_lit_Bool
  | x, y => decide (x = y)
def smt_lit_zleq : smt_lit_Int -> smt_lit_Int -> smt_lit_Bool
  | x, y => decide (x <= y)
def smt_lit_zlt : smt_lit_Int -> smt_lit_Int -> smt_lit_Bool
  | x, y => decide (x < y)
def smt_lit_div_total : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | x, y => x/y
def smt_lit_mod_total : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | x, y => x%y
def smt_lit_zexp_total (x : smt_lit_Int) (y : smt_lit_Int) : smt_lit_Int :=
  if y < 0 then 0 else (x ^ (Int.toNat y))
def smt_lit_int_pow2 (n : smt_lit_Int) : smt_lit_Int :=
  (smt_lit_zexp_total 2 n)
def smt_lit_piand : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) &&& (BitVec.ofInt (Int.toNat w) y)).toInt

-- Rational arithmetic
def smt_lit_mk_rational : smt_lit_Int -> smt_lit_Int -> smt_lit_Rat
  | x, y => x/y
def smt_lit_qplus : smt_lit_Rat -> smt_lit_Rat -> smt_lit_Rat
  | x, y => x+y
def smt_lit_qmult : smt_lit_Rat -> smt_lit_Rat -> smt_lit_Rat
  | x, y => x*y
def smt_lit_qneg : smt_lit_Rat -> smt_lit_Rat
  | x => -x
def smt_lit_qeq : smt_lit_Rat -> smt_lit_Rat -> smt_lit_Bool
  | x, y => decide (x = y)
def smt_lit_qleq : smt_lit_Rat -> smt_lit_Rat -> smt_lit_Bool
  | x, y => decide (x <= y)
def smt_lit_qlt : smt_lit_Rat -> smt_lit_Rat -> smt_lit_Bool
  | x, y => decide (x < y)
def smt_lit_qdiv_total : smt_lit_Rat -> smt_lit_Rat -> smt_lit_Rat
  | x, y => x/y

-- Conversions
def smt_lit_to_int : smt_lit_Rat -> smt_lit_Int
  | x => (Rat.floor x)
def smt_lit_to_real : smt_lit_Int -> smt_lit_Rat
  | x => (smt_lit_mk_rational x 1)

-- Strings
def smt_lit_str_len : smt_lit_String -> smt_lit_Int
  | x => Int.ofNat x.length
def smt_lit_str_concat : smt_lit_String -> smt_lit_String -> smt_lit_String
  | x, y => x ++ y
def smt_lit_str_substr (s : smt_lit_String) (i n : smt_lit_Int) : smt_lit_String :=
  let len : Int := (smt_lit_str_len s)
  if i < 0 || n <= 0 || i >= len then
    ""
  else
    let start : Nat := Int.toNat i
    let take  : Nat := Int.toNat (min n (len - i))
    String.Pos.Raw.extract s ⟨start⟩ ⟨start + take⟩
partial def smt_lit_str_indexof_rec (s t : smt_lit_String) (i len : Nat) : smt_lit_Int :=
  if (i+len)>(smt_lit_str_len s) then
    -1
  else if String.Pos.Raw.substrEq s ⟨i⟩ t ⟨0⟩ len then
    i
  else
    smt_lit_str_indexof_rec s t (i+1) len
def smt_lit_str_indexof (s t : smt_lit_String) (i : smt_lit_Int) : smt_lit_Int :=
  if i < 0 then
    -1
  else
    (smt_lit_str_indexof_rec s t (Int.toNat i) (Int.toNat (smt_lit_str_len t)))
def smt_lit_str_to_code (s : smt_lit_String) : smt_lit_Int :=
  match s.toList with
  | [c] => Int.ofNat c.toNat
  | _   => -1
def smt_lit_str_from_code (i : smt_lit_Int) : smt_lit_String :=
  if (0 <= i && i <= 196608) then
    String.singleton (Char.ofNat (Int.toNat i))
  else
    ""
def smt_lit_streq : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | x, y => decide (x = y)


def smt_lit_pow2 : smt_lit_Int -> smt_lit_Int
  | i => (smt_lit_int_pow2 i)


def smt_lit_bit : smt_lit_Int -> smt_lit_Int -> smt_lit_Bool
  | x, i => (smt_lit_zeq 1 (smt_lit_mod_total (smt_lit_div_total x (smt_lit_pow2 i)) 2))


def smt_lit_msb : smt_lit_Int -> smt_lit_Int -> smt_lit_Bool
  | w, n => (smt_lit_bit n (smt_lit_zplus w (smt_lit_zneg 1)))


def smt_lit_binary_and : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n1, n2 => (smt_lit_ite (smt_lit_zeq w 0) 0 (smt_lit_piand w n1 n2))


def smt_lit_binary_or : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n1, n2 => (smt_lit_zplus n1 (smt_lit_zplus n2 (smt_lit_zneg (smt_lit_ite (smt_lit_zeq w 0) 0 (smt_lit_piand w n1 n2)))))


def smt_lit_binary_xor : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n1, n2 => (smt_lit_zplus n1 (smt_lit_zplus n2 (smt_lit_zneg (smt_lit_zmult 2 (smt_lit_ite (smt_lit_zeq w 0) 0 (smt_lit_piand w n1 n2))))))


def smt_lit_binary_not : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n => (smt_lit_zplus (smt_lit_pow2 w) (smt_lit_zneg (smt_lit_zplus n 1)))


def smt_lit_binary_max : smt_lit_Int -> smt_lit_Int
  | w => (smt_lit_zplus (smt_lit_pow2 w) (smt_lit_zneg 1))


def smt_lit_binary_uts : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n => (smt_lit_zplus (smt_lit_zmult 2 (smt_lit_mod_total n (smt_lit_pow2 (smt_lit_zplus w (smt_lit_zneg 1))))) (smt_lit_zneg n))


def smt_lit_binary_concat : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w1, n1, w2, n2 => (smt_lit_zplus (smt_lit_zmult n1 (smt_lit_pow2 w2)) n2)


def smt_lit_binary_extract : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n, x1, x2 => (smt_lit_div_total n (smt_lit_pow2 x2))

-- Natural numbers

abbrev smt_lit_Nat := Nat
def smt_lit_int_to_nat (x : smt_lit_Int) : smt_lit_Nat :=
  (Int.toNat x)
def smt_lit_nat_to_int (x : smt_lit_Nat) : smt_lit_Int :=
  (Int.ofNat x)
def smt_lit_nateq : smt_lit_Nat -> smt_lit_Nat -> smt_lit_Bool
  | x, y => decide (x = y)
syntax "smt_lit_nat_zero" : term
macro_rules
  | `(smt_lit_nat_zero) => `(Nat.zero)
syntax "smt_lit_nat_succ " term : term
macro_rules
  | `(smt_lit_nat_succ $x) => `(Nat.succ $x)

end SmtEval


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
abbrev smt_lit_streq : SmtEval.smt_lit_streq

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
def smt_lit_wrong_apply_sel_id : smt_lit_Int := -4

mutual

/- 
SMT-LIB types.
-/
inductive SmtType : Type where
  | None : SmtType
  | Bool : SmtType
  | Int : SmtType

deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
  | None : SmtTerm
  | Boolean : smt_lit_Bool -> SmtTerm
  | Numeral : smt_lit_Int -> SmtTerm
  | Apply : SmtTerm -> SmtTerm -> SmtTerm
  | eq : SmtTerm
  | not : SmtTerm
  | or : SmtTerm
  | and : SmtTerm
  | imp : SmtTerm

deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB values.
-/
inductive SmtValue : Type where
  | NotValue : SmtValue
  | Boolean : smt_lit_Bool -> SmtValue
  | Numeral : smt_lit_Int -> SmtValue

deriving Repr, DecidableEq, Inhabited

end

/-
SMT-LIB model
-/
abbrev SmtModel := Int -- FIXME


/- Type equality -/
def smt_lit_Teq : SmtType -> SmtType -> smt_lit_Bool
  | x, y => decide (x = y)
/- Value equality -/
def smt_lit_veq : SmtValue -> SmtValue -> smt_lit_Bool
  | x, y => decide (x = y)

/- Definition of SMT-LIB model semantics -/

mutual

def __smtx_typeof_value : SmtValue -> SmtType
  | (SmtValue.Boolean b) => SmtType.Bool
  | (SmtValue.Numeral n) => SmtType.Int
  | v => SmtType.None


def __smtx_model_eval_eq (t1 : SmtValue) (t2 : SmtValue) : SmtValue :=
  (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) (__smtx_typeof_value t2)) (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) SmtType.None) SmtValue.NotValue (SmtValue.Boolean (smt_lit_veq t1 t2))) SmtValue.NotValue)

def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (smt_lit_not x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_or : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_or x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_and x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval_imp (x1 : SmtValue) (x2 : SmtValue) : SmtValue :=
  (__smtx_model_eval_or (__smtx_model_eval_not x1) x2)

def __smtx_model_eval (M : SmtModel) : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Apply SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval M x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x1) x2) => (__smtx_model_eval_and (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp x1) x2) => (__smtx_model_eval_imp (__smtx_model_eval M x1) (__smtx_model_eval M x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) => (__smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2))
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

namespace Eo

/- Eunoia literal evaluation defined -/

abbrev eo_lit_Bool := SmtEval.smt_lit_Bool
abbrev eo_lit_Int := SmtEval.smt_lit_Int
abbrev eo_lit_Rat := SmtEval.smt_lit_Rat
abbrev eo_lit_String := SmtEval.smt_lit_String

def eo_lit_ite {T : Type} (c : eo_lit_Bool) (t e : T) : T :=
  if c then t else e
abbrev eo_lit_not := SmtEval.smt_lit_not
abbrev eo_lit_and := SmtEval.smt_lit_and
abbrev eo_lit_iff := SmtEval.smt_lit_iff
abbrev eo_lit_or := SmtEval.smt_lit_or
abbrev eo_lit_xor := SmtEval.smt_lit_xor
abbrev eo_lit_zplus := SmtEval.smt_lit_zplus
abbrev eo_lit_zmult := SmtEval.smt_lit_zmult
abbrev eo_lit_zneg := SmtEval.smt_lit_zneg
abbrev eo_lit_zeq := SmtEval.smt_lit_zeq
abbrev eo_lit_zleq := SmtEval.smt_lit_zleq
abbrev eo_lit_zlt := SmtEval.smt_lit_zlt
abbrev eo_lit_div_total := SmtEval.smt_lit_div_total
abbrev eo_lit_mod_total := SmtEval.smt_lit_mod_total
abbrev eo_lit_zexp_total := SmtEval.smt_lit_zexp_total
abbrev eo_lit_int_pow2 := SmtEval.smt_lit_int_pow2
abbrev eo_lit_piand := SmtEval.smt_lit_piand
abbrev eo_lit_mk_rational := SmtEval.smt_lit_mk_rational
abbrev eo_lit_qplus := SmtEval.smt_lit_qplus
abbrev eo_lit_qmult := SmtEval.smt_lit_qmult
abbrev eo_lit_qneg := SmtEval.smt_lit_qneg
abbrev eo_lit_qeq := SmtEval.smt_lit_qeq
abbrev eo_lit_qleq := SmtEval.smt_lit_qleq
abbrev eo_lit_qlt := SmtEval.smt_lit_qlt
abbrev eo_lit_qdiv_total := SmtEval.smt_lit_qdiv_total
abbrev eo_lit_to_int := SmtEval.smt_lit_to_int
abbrev eo_lit_to_real := SmtEval.smt_lit_to_real
abbrev eo_lit_str_len := SmtEval.smt_lit_str_len
abbrev eo_lit_str_concat := SmtEval.smt_lit_str_concat
abbrev eo_lit_str_substr := SmtEval.smt_lit_str_substr
abbrev eo_lit_str_indexof := SmtEval.smt_lit_str_indexof
abbrev eo_lit_str_to_code := SmtEval.smt_lit_str_to_code
abbrev eo_lit_str_from_code := SmtEval.smt_lit_str_from_code
abbrev eo_lit_streq := SmtEval.smt_lit_streq

abbrev eo_lit_bit := SmtEval.smt_lit_bit
abbrev eo_lit_msb := SmtEval.smt_lit_msb
abbrev eo_lit_binary_and := SmtEval.smt_lit_binary_and
abbrev eo_lit_binary_or := SmtEval.smt_lit_binary_or
abbrev eo_lit_binary_xor := SmtEval.smt_lit_binary_xor
abbrev eo_lit_binary_not := SmtEval.smt_lit_binary_not
abbrev eo_lit_binary_max := SmtEval.smt_lit_binary_max
abbrev eo_lit_binary_uts := SmtEval.smt_lit_binary_uts
abbrev eo_lit_binary_concat := SmtEval.smt_lit_binary_concat
abbrev eo_lit_binary_extract := SmtEval.smt_lit_binary_extract

abbrev eo_lit_Nat := SmtEval.smt_lit_Nat
abbrev eo_lit_int_to_nat := SmtEval.smt_lit_int_to_nat
abbrev eo_lit_nat_to_int := SmtEval.smt_lit_nat_to_int
abbrev eo_lit_nateq := SmtEval.smt_lit_nateq
syntax "eo_lit_nat_zero" : term
macro_rules
  | `(eo_lit_nat_zero) => `(Nat.zero)
syntax "eo_lit_nat_succ " term : term
macro_rules
  | `(eo_lit_nat_succ $x) => `(Nat.succ $x)

instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

mutual

/- Term definition -/
inductive Term : Type where
$LEAN_TERM_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/-
Eunoia datatypes.
-/
inductive Datatype : Type where
  | null : Datatype
  | sum : DatatypeCons -> Datatype -> Datatype
deriving Repr, DecidableEq, Inhabited

/-
Eunoia datatype constructors.
-/
inductive DatatypeCons : Type where
  | unit : DatatypeCons
  | cons : Term -> DatatypeCons -> DatatypeCons
deriving Repr, DecidableEq, Inhabited

end

/- Term equality -/
def eo_lit_teq : Term -> Term -> eo_lit_Bool
  | x, y => decide (x = y)

/- Term less than, based on arbitrary ordering -/
def eo_lit_tcmp (a b : Term) : eo_lit_Bool :=
  match compare a b with
  | Ordering.lt => true
  | _ => false

/- Used for defining hash -/
def eo_lit_thash : Term -> eo_lit_Int
  | _ => 0 -- FIXME

/- Proofs -/
inductive Proof : Type where
  | pf : Term -> Proof
  | Stuck : Proof

/- Definition of Eunoia signature -/

mutual

$LEAN_DEFS$

end

/- Definition of the checker -/

abbrev CIndex := eo_lit_Int

/-
-/
inductive CIndexList : Type where
  | nil : CIndexList
  | cons : CIndex -> CIndexList -> CIndexList
deriving Repr, Inhabited

/-
-/
inductive CArgList : Type where
  | nil : CArgList
  | cons : Term -> CArgList -> CArgList
deriving Repr, Inhabited

/-
-/
inductive CStateObj : Type where
  | assume : Term -> CStateObj
  | assume_push : Term -> CStateObj
  | proven : Term -> CStateObj
  | Stuck : CStateObj
deriving Repr, Inhabited

/-
-/
inductive CState : Type where
  | nil : CState
  | cons : CStateObj -> CState -> CState
  | Stuck : CState
deriving Repr, Inhabited

/-
-/
inductive CRule : Type where
$LEAN_CHECKER_RULE_DEF$
deriving Repr, Inhabited

/-
-/
inductive CCmd : Type where
$LEAN_CHECKER_CMD_DEF$
deriving Repr, Inhabited

/-
-/
inductive CCmdList : Type where
  | nil : CCmdList
  | cons : CCmd -> CCmdList -> CCmdList
deriving Repr, Inhabited

$LEAN_CHECKER_DEFS$

/-- API for logos -/
def logos_init_state : CState := CState.nil
def logos_invoke_assume (s : CState) (A : Term) : CState := (CState.cons (CStateObj.assume A) s)
def logos_invoke_cmd (s : CState) (c :CCmd) : CState := (__eo_invoke_cmd s c)
def logos_state_is_refutation (s : CState) : eo_lit_Bool := (__eo_state_is_refutation s)

end Eo


open Eo
open Smtm

/- Definition of refutation -/

inductive eo_is_refutation : Term -> CCmdList -> Prop
  | intro (F : Term) (c : CCmdList) : 
    (__eo_checker_is_refutation F c) = true -> (eo_is_refutation F c)


/-
A definition of terms in the object language.
This is to be defined externally.
-/
abbrev Object_Term := SmtTerm

/-
A predicate defining a relation on terms in the object language and Booleans
such that (s,b) is true if s evaluates to b.
This is to be defined externally.
-/
abbrev obj_interprets := smt_interprets


/-
Definitions for eo_is_obj
-/
mutual

def __eo_to_smt_type : Term -> SmtType
  | T => SmtType.None


def __eo_to_smt : Term -> SmtTerm
  | y => SmtTerm.None


end 

/-
An inductive predicate defining the correspondence between Eunoia terms
and terms in the object language.
(t,s) is true if the Eunoia term represents a term s in the object language.
This is to be custom defined in the Eunoia-to-Lean compiler based on the
target definition of Object_Term.
-/
inductive eo_is_obj : Term -> Object_Term -> Prop
  | intro (x : Term) : eo_is_obj x (__eo_to_smt x)


/-
A predicate defining when a Eunoia term corresponds to an object term that
evaluates to true or false.
(t,b) is true if t is a Eunoia term corresponding to an object term that
evaluates to b.
-/
def eo_interprets (t : Term) (b : Bool) : Prop :=
  exists (s : Object_Term), (eo_is_obj t s) /\ (obj_interprets s b)

/- The theorem statements -/

/- correctness theorem for __eo_prog_scope -/
theorem correct___eo_prog_scope (x1 x2 : Term) :
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_scope x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_contra -/
theorem correct___eo_prog_contra (x1 x2 : Term) :
  (eo_interprets x1 true) ->
  (eo_interprets x2 true) ->
  (Not (eo_interprets (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_symm -/
theorem correct___eo_prog_symm (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_symm (Proof.pf x1)) false)) :=
by
  sorry



/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  (eo_is_refutation F pf) ->
  (eo_interprets F false) :=
by
  sorry
