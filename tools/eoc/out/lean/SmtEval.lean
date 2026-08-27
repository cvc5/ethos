module

public import Init

public section

set_option linter.unusedVariables false

namespace SmtEval

-- Not a block: SmtValue carries a Rational constructor whatever the input
-- signature is, and derives Ord, so this instance is always needed.
instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

-- A proof written against the published tree names its strings with this, so
-- it is kept for a signature that has no string of its own to build.

-- The part of the native layer that every generated file can see. What comes
-- out here is what more than one of them reaches, since a definition only one
-- reaches is emitted into that file instead. See
-- LeanMetaReduce::placeNativeDefs and plugins/lean_meta/lean_meta_native.lean.
abbrev native_Bool := Bool

abbrev native_Int := Int

abbrev native_Rat := Rat

abbrev native_Nat := Nat

abbrev native_Char := Nat

abbrev native_String := List native_Char

def native_string_lit (s : String) : native_String :=
  s.toList.map Char.toNat

def native_ite {T : Type} (c : native_Bool) (t e : T) : T :=
  if c then t else e

def native_not : native_Bool -> native_Bool
  | x => Bool.not x

def native_and : native_Bool -> native_Bool -> native_Bool
  | x, y => x && y

def native_zeq : native_Int -> native_Int -> native_Bool
  | x, y => decide (x = y)

def native_mod_total : native_Int -> native_Int -> native_Int
  | x, y => x%y

def native_zexp_total (x : native_Int) (y : native_Int) : native_Int :=
  if y < 0 then 0 else (x ^ (Int.toNat y))

def native_int_pow2 (n : native_Int) : native_Int :=
  (native_zexp_total 2 n)

def native_mk_rational : native_Int -> native_Int -> native_Rat
  | x, y => x/y

def native_streq : native_String -> native_String -> native_Bool
  | x, y => decide (x = y)

syntax "native_nat_zero" : term
macro_rules
  | `(native_nat_zero) => `(Nat.zero)

syntax "native_nat_succ " term : term
macro_rules
  | `(native_nat_succ $x) => `(Nat.succ $x)

-- Strings of the checker. The Eunoia string operators are over Lean strings,
-- where the SMT-LIB ones are over sequences of values, so the two are
-- different functions of the layer rather than one shared by both.


end SmtEval
