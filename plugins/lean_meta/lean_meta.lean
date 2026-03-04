set_option linter.unusedVariables false

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
def smt_lit_div : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | x, y => x/y
def smt_lit_mod : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | x, y => x%y
def smt_lit_int_pow2 (n : smt_lit_Int) : smt_lit_Int :=
  if n < 0 then 0 else (2 ^ (Int.toNat n))
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
def smt_lit_qdiv : smt_lit_Rat -> smt_lit_Rat -> smt_lit_Rat
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


def __smtx_pow2 : smt_lit_Int -> smt_lit_Int
  | i => (smt_lit_int_pow2 i)


def __smtx_bit : smt_lit_Int -> smt_lit_Int -> smt_lit_Bool
  | x, i => (smt_lit_zeq 1 (smt_lit_mod (smt_lit_div x (__smtx_pow2 i)) 2))


def __smtx_msb : smt_lit_Int -> smt_lit_Int -> smt_lit_Bool
  | w, n => (__smtx_bit n (smt_lit_zplus w (smt_lit_zneg 1)))


def __smtx_binary_or : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n1, n2 => (smt_lit_zplus n1 (smt_lit_zplus n2 (smt_lit_zneg (smt_lit_ite (smt_lit_zeq w 0) 0 (smt_lit_piand w n1 n2)))))


def __smtx_binary_xor : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n1, n2 => (smt_lit_zplus n1 (smt_lit_zplus n2 (smt_lit_zneg (smt_lit_zmult 2 (smt_lit_ite (smt_lit_zeq w 0) 0 (smt_lit_piand w n1 n2))))))


def __smtx_binary_not : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n => (smt_lit_zplus (__smtx_pow2 w) (smt_lit_zneg (smt_lit_zplus n 1)))


def __smtx_binary_max : smt_lit_Int -> smt_lit_Int
  | w => (smt_lit_zplus (__smtx_pow2 w) (smt_lit_zneg 1))


def __smtx_binary_uts : smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n => (smt_lit_zplus (smt_lit_zmult 2 (smt_lit_mod n (__smtx_pow2 (smt_lit_zplus w (smt_lit_zneg 1))))) (smt_lit_zneg n))


def __smtx_binary_concat : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w1, n1, w2, n2 => (smt_lit_zplus (smt_lit_zmult n1 (__smtx_pow2 w2)) n2)


def __smtx_binary_extract : smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int -> smt_lit_Int
  | w, n, x1, x2 => (smt_lit_div n (__smtx_pow2 x2))

end SmtEval

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
abbrev eo_lit_div := SmtEval.smt_lit_div
abbrev eo_lit_mod := SmtEval.smt_lit_mod
abbrev eo_lit_mk_rational := SmtEval.smt_lit_mk_rational
abbrev eo_lit_qplus := SmtEval.smt_lit_qplus
abbrev eo_lit_qmult := SmtEval.smt_lit_qmult
abbrev eo_lit_qneg := SmtEval.smt_lit_qneg
abbrev eo_lit_qeq := SmtEval.smt_lit_qeq
abbrev eo_lit_qleq := SmtEval.smt_lit_qleq
abbrev eo_lit_qlt := SmtEval.smt_lit_qlt
abbrev eo_lit_qdiv := SmtEval.smt_lit_qdiv
abbrev eo_lit_to_int := SmtEval.smt_lit_to_int
abbrev eo_lit_to_real := SmtEval.smt_lit_to_real
abbrev eo_lit_str_len := SmtEval.smt_lit_str_len
abbrev eo_lit_str_concat := SmtEval.smt_lit_str_concat
abbrev eo_lit_str_substr := SmtEval.smt_lit_str_substr
abbrev eo_lit_str_indexof := SmtEval.smt_lit_str_indexof
abbrev eo_lit_str_to_code := SmtEval.smt_lit_str_to_code
abbrev eo_lit_str_from_code := SmtEval.smt_lit_str_from_code
abbrev eo_lit_piand := SmtEval.smt_lit_piand

abbrev __smtx_pow2 := SmtEval.__smtx_pow2
abbrev __smtx_bit := SmtEval.__smtx_bit
abbrev __smtx_msb := SmtEval.__smtx_msb
abbrev __smtx_binary_or := SmtEval.__smtx_binary_or
abbrev __smtx_binary_xor := SmtEval.__smtx_binary_xor
abbrev __smtx_binary_not := SmtEval.__smtx_binary_not
abbrev __smtx_binary_max := SmtEval.__smtx_binary_max
abbrev __smtx_binary_uts := SmtEval.__smtx_binary_uts
abbrev __smtx_binary_concat := SmtEval.__smtx_binary_concat
abbrev __smtx_binary_extract := SmtEval.__smtx_binary_extract

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

end Eo
