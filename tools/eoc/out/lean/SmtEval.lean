set_option linter.unusedVariables false

namespace SmtEval

abbrev native_Bool := Bool
abbrev native_Int := Int
abbrev native_Rat := Rat
abbrev native_String := String
abbrev native_Nat := Nat
abbrev native_Char := Char

instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

/- Evaluation functions -/

def native_ite {T : Type} (c : native_Bool) (t e : T) : T :=
  if c then t else e
def native_not : native_Bool -> native_Bool
  | x => Bool.not x
def native_and : native_Bool -> native_Bool -> native_Bool
  | x, y => x && y
def native_iff : native_Bool -> native_Bool -> native_Bool
  | x, y => decide (x = y)
def native_or : native_Bool -> native_Bool -> native_Bool
  | x, y => x || y
def native_xor : native_Bool -> native_Bool -> native_Bool
  | x, y => Bool.xor x y

-- Integer arithmetic
def native_zplus : native_Int -> native_Int -> native_Int
  | x, y => x+y
def native_zmult : native_Int -> native_Int -> native_Int
  | x, y => x*y
def native_zneg : native_Int -> native_Int
  | x => -x
def native_zeq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x = y)
def native_zleq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x <= y)
def native_zlt : native_Int -> native_Int -> native_Bool
  | x, y => decide (x < y)
def native_div_total : native_Int -> native_Int -> native_Int
  | x, y => x/y
def native_mod_total : native_Int -> native_Int -> native_Int
  | x, y => x%y
def native_zexp_total (x : native_Int) (y : native_Int) : native_Int :=
  if y < 0 then 0 else (x ^ (Int.toNat y))
def native_int_pow2 (n : native_Int) : native_Int :=
  (native_zexp_total 2 n)
def native_piand : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) &&& (BitVec.ofInt (Int.toNat w) y)).toInt
def native_pior : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ||| (BitVec.ofInt (Int.toNat w) y)).toInt
def native_pixor : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ^^^ (BitVec.ofInt (Int.toNat w) y)).toInt

-- Rational arithmetic
def native_mk_rational : native_Int -> native_Int -> native_Rat
  | x, y => x/y
def native_qplus : native_Rat -> native_Rat -> native_Rat
  | x, y => x+y
def native_qmult : native_Rat -> native_Rat -> native_Rat
  | x, y => x*y
def native_qneg : native_Rat -> native_Rat
  | x => -x
def native_qeq : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x = y)
def native_qleq : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x <= y)
def native_qlt : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x < y)
def native_qdiv_total : native_Rat -> native_Rat -> native_Rat
  | x, y => x/y
def native_qexp_total (x : native_Rat) (y : native_Int) : native_Rat :=
  if y < 0 then (native_mk_rational 0 1) else (x ^ (Int.toNat y))

-- Conversions
def native_to_int : native_Rat -> native_Int
  | x => (Rat.floor x)
def native_to_real : native_Int -> native_Rat
  | x => (native_mk_rational x 1)

-- Strings
def native_nat_to_char : native_Nat -> native_Char
  | x => (Char.ofNat x)
def native_str_to_code (s : native_String) : native_Int :=
  match s.toList with
  | [c] => Int.ofNat c.toNat
  | _   => -1
def native_str_from_code (i : native_Int) : native_String :=
  if (0 <= i && i <= 196608) then
    String.singleton (native_nat_to_char (Int.toNat i))
  else
    ""
def native_streq : native_String -> native_String -> native_Bool
  | x, y => decide (x = y)

def native_bit : native_Int -> native_Int -> native_Bool
  | x, i => (native_zeq 1 (native_mod_total (native_div_total x (native_int_pow2 i)) 2))

def native_msb : native_Int -> native_Int -> native_Bool
  | w, n => (native_bit n (native_zplus w (native_zneg 1)))

def native_binary_and : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (native_piand w n1 n2))

def native_binary_or : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (native_pior w n1 n2))

def native_binary_xor : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (native_pixor w n1 n2))

def native_binary_not : native_Int -> native_Int -> native_Int
  | w, n => (native_zplus (native_int_pow2 w) (native_zneg (native_zplus n 1)))

def native_binary_max : native_Int -> native_Int
  | w => (native_zplus (native_int_pow2 w) (native_zneg 1))

def native_binary_uts : native_Int -> native_Int -> native_Int
  | w, n => (native_zplus (native_zmult 2 (native_mod_total n (native_int_pow2 (native_zplus w (native_zneg 1))))) (native_zneg n))

def native_binary_concat : native_Int -> native_Int -> native_Int -> native_Int -> native_Int
  | w1, n1, w2, n2 => (native_zplus (native_zmult n1 (native_int_pow2 w2)) n2)

def native_binary_extract : native_Int -> native_Int -> native_Int -> native_Int -> native_Int
  | w, n, x1, x2 => (native_div_total n (native_int_pow2 x2))

-- Natural numbers

def native_int_to_nat (x : native_Int) : native_Nat :=
  (Int.toNat x)
def native_nat_to_int (x : native_Nat) : native_Int :=
  (Int.ofNat x)
def native_nateq : native_Nat -> native_Nat -> native_Bool
  | x, y => decide (x = y)
def native_nat_plus : native_Nat -> native_Nat -> native_Nat
  | x, y => (x+y)
syntax "native_nat_zero" : term
macro_rules
  | `(native_nat_zero) => `(Nat.zero)
syntax "native_nat_succ " term : term
macro_rules
  | `(native_nat_succ $x) => `(Nat.succ $x)

end SmtEval
