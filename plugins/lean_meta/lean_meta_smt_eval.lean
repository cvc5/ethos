module

public import Init

public section

set_option linter.unusedVariables false

-- The native definitions below are the ones this signature reaches; the rest
-- of the layer is left out. See LeanMetaReduce::trimNativeDefs.

namespace SmtEval

-- $native native_Bool
abbrev native_Bool := Bool
-- $native native_Int
abbrev native_Int := Int
-- $native native_Rat
abbrev native_Rat := Rat
-- $native native_Nat
abbrev native_Nat := Nat
-- $native native_Char
abbrev native_Char := Nat
-- $native native_String
abbrev native_String := List native_Char

-- $native native_char_valid
def native_char_valid (c : native_Char) : native_Bool :=
  c < 196608

-- $native native_string_valid
def native_string_valid (s : native_String) : native_Bool :=
  s.all native_char_valid

-- A proof written against the published tree names its strings with this, so
-- it is kept for a signature that has no string of its own to build.
-- $native-root native_string_lit
-- $native native_string_lit
def native_string_lit (s : String) : native_String :=
  s.toList.map Char.toNat

-- $native native_string_of_lean_string
def native_string_of_lean_string (s : String) : native_String :=
  native_string_lit s

-- $native native_string_prefix_eq
def native_string_prefix_eq : native_String -> native_String -> native_Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: cs, d :: ds => decide (c = d) && native_string_prefix_eq cs ds
-- $native-end

-- Not a block: SmtValue carries a Rational constructor whatever the input
-- signature is, and derives Ord, so this instance is always needed.
instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

/- Evaluation functions -/

-- $native native_ite
def native_ite {T : Type} (c : native_Bool) (t e : T) : T :=
  if c then t else e
-- $native native_not
def native_not : native_Bool -> native_Bool
  | x => Bool.not x
-- $native native_and
def native_and : native_Bool -> native_Bool -> native_Bool
  | x, y => x && y
-- $native native_iff
def native_iff : native_Bool -> native_Bool -> native_Bool
  | x, y => decide (x = y)
-- $native native_or
def native_or : native_Bool -> native_Bool -> native_Bool
  | x, y => x || y
-- $native native_xor
def native_xor : native_Bool -> native_Bool -> native_Bool
  | x, y => Bool.xor x y
-- $native-end

-- Integer arithmetic

-- $native native_zplus
def native_zplus : native_Int -> native_Int -> native_Int
  | x, y => x+y
-- $native native_zmult
def native_zmult : native_Int -> native_Int -> native_Int
  | x, y => x*y
-- $native native_zneg
def native_zneg : native_Int -> native_Int
  | x => -x
-- $native native_zeq
def native_zeq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x = y)
-- $native native_zleq
def native_zleq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x <= y)
-- $native native_zlt
def native_zlt : native_Int -> native_Int -> native_Bool
  | x, y => decide (x < y)
-- $native native_div_total
def native_div_total : native_Int -> native_Int -> native_Int
  | x, y => x/y
-- $native native_mod_total
def native_mod_total : native_Int -> native_Int -> native_Int
  | x, y => x%y
-- $native native_zexp_total
def native_zexp_total (x : native_Int) (y : native_Int) : native_Int :=
  if y < 0 then 0 else (x ^ (Int.toNat y))
-- $native native_int_log_rec
-- Helper for native_int_log: repeatedly divides `remaining` by `base`, counting
-- the steps until it drops below `base`. `fuel` bounds the recursion (the caller
-- passes the value itself, which is always at least the number of steps when
-- base >= 2).
def native_int_log_rec (base : native_Nat) : native_Nat -> native_Nat -> native_Nat
  | 0, _ => 0
  | fuel + 1, remaining =>
    if remaining < base then 0 else 1 + native_int_log_rec base fuel (remaining / base)
-- $native native_int_log
-- The (rounded-down) integer logarithm of `v` in base `b`, i.e. the greatest
-- m >= 0 such that b^m <= v, or 0 when b <= 1 or v <= 0. This aligns with Lean's
-- `Nat.log` and is the integer inverse of native_zexp_total.
def native_int_log (b : native_Int) (v : native_Int) : native_Int :=
  let base := Int.toNat b
  let value := Int.toNat v
  if base <= 1 || value == 0 then 0 else Int.ofNat (native_int_log_rec base value value)
-- $native native_int_pow2
def native_int_pow2 (n : native_Int) : native_Int :=
  (native_zexp_total 2 n)
-- $native native_piand
def native_piand : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) &&& (BitVec.ofInt (Int.toNat w) y)).toInt
-- $native native_pior
def native_pior : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ||| (BitVec.ofInt (Int.toNat w) y)).toInt
-- $native native_pixor
def native_pixor : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ^^^ (BitVec.ofInt (Int.toNat w) y)).toInt
-- $native-end

-- Rational arithmetic

-- $native native_mk_rational
def native_mk_rational : native_Int -> native_Int -> native_Rat
  | x, y => x/y
-- $native native_qplus
def native_qplus : native_Rat -> native_Rat -> native_Rat
  | x, y => x+y
-- $native native_qmult
def native_qmult : native_Rat -> native_Rat -> native_Rat
  | x, y => x*y
-- $native native_qneg
def native_qneg : native_Rat -> native_Rat
  | x => -x
-- $native native_qeq
def native_qeq : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x = y)
-- $native native_qleq
def native_qleq : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x <= y)
-- $native native_qlt
def native_qlt : native_Rat -> native_Rat -> native_Bool
  | x, y => decide (x < y)
-- $native native_qdiv_total
def native_qdiv_total : native_Rat -> native_Rat -> native_Rat
  | x, y => x/y
-- $native native_qexp_total
def native_qexp_total (x : native_Rat) (y : native_Int) : native_Rat :=
  if y < 0 then (native_mk_rational 0 1) else (x ^ (Int.toNat y))
-- $native-end

-- Conversions

-- $native native_to_int
def native_to_int : native_Rat -> native_Int
  | x => (Rat.floor x)
-- $native native_to_real
def native_to_real : native_Int -> native_Rat
  | x => (native_mk_rational x 1)
-- $native-end

-- Strings

-- $native native_str_to_code
def native_str_to_code (s : native_String) : native_Int :=
  match s with
  | [c] => if native_char_valid c then Int.ofNat c else -1
  | _   => -1
-- $native native_str_from_code
def native_str_from_code (i : native_Int) : native_String :=
  if (0 <= i && (native_char_valid (Int.toNat i))) then
    [(Int.toNat i)]
  else
    native_string_lit ""
-- $native native_streq
def native_streq : native_String -> native_String -> native_Bool
  | x, y => decide (x = y)

-- $native native_bit
def native_bit : native_Int -> native_Int -> native_Bool
  | x, i => (native_zeq 1 (native_mod_total (native_div_total x (native_int_pow2 i)) 2))

-- $native native_msb
def native_msb : native_Int -> native_Int -> native_Bool
  | w, n => (native_bit n (native_zplus w (native_zneg 1)))

-- $native native_binary_and
def native_binary_and : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (native_piand w n1 n2))

-- $native native_binary_or
def native_binary_or : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (native_pior w n1 n2))

-- $native native_binary_xor
def native_binary_xor : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (native_pixor w n1 n2))

-- $native native_binary_not
def native_binary_not : native_Int -> native_Int -> native_Int
  | w, n => (native_zplus (native_int_pow2 w) (native_zneg (native_zplus n 1)))

-- $native native_binary_max
def native_binary_max : native_Int -> native_Int
  | w => (native_zplus (native_int_pow2 w) (native_zneg 1))

-- $native native_binary_uts
def native_binary_uts : native_Int -> native_Int -> native_Int
  | w, n => (native_zplus (native_zmult 2 (native_mod_total n (native_int_pow2 (native_zplus w (native_zneg 1))))) (native_zneg n))

-- $native native_binary_concat
def native_binary_concat : native_Int -> native_Int -> native_Int -> native_Int -> native_Int
  | w1, n1, w2, n2 => (native_zplus (native_zmult n1 (native_int_pow2 w2)) n2)

-- $native native_binary_extract
def native_binary_extract : native_Int -> native_Int -> native_Int -> native_Int -> native_Int
  -- The caller masks this quotient to width x1 - x2 + 1; w and x1 are carried
  -- here only to match the native EO operation's signature.
  | w, n, x1, x2 => (native_div_total n (native_int_pow2 x2))
-- $native-end

-- Natural numbers

-- $native native_int_to_nat
def native_int_to_nat (x : native_Int) : native_Nat :=
  (Int.toNat x)
-- $native native_nat_to_int
def native_nat_to_int (x : native_Nat) : native_Int :=
  (Int.ofNat x)
-- $native native_nateq
def native_nateq : native_Nat -> native_Nat -> native_Bool
  | x, y => decide (x = y)
-- $native native_nat_plus
def native_nat_plus : native_Nat -> native_Nat -> native_Nat
  | x, y => (x+y)
-- $native native_nat_zero
syntax "native_nat_zero" : term
macro_rules
  | `(native_nat_zero) => `(Nat.zero)
-- $native native_nat_succ
syntax "native_nat_succ " term : term
macro_rules
  | `(native_nat_succ $x) => `(Nat.succ $x)
-- $native-end

end SmtEval
