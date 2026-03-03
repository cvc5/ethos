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
def smt_lit_str_indexof_rec (s t : smt_lit_String) (i len : Nat) : smt_lit_Int :=
  if (i+len)>(smt_lit_str_len s) then
    -1
  else if String.Pos.Raw.substrEq s ⟨i⟩ t ⟨0⟩ len then
    i
  else
    smt_lit_str_indexof_rec s t (i+1) len
decreasing_by sorry  -- FIXME
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
