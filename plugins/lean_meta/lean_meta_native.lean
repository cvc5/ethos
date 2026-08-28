-- The native layer: every definition the generated Lean is allowed to call
-- that the compiler does not write itself.
--
-- The layer is one library rather than a part of each file that happens to
-- use it: a definition is written once, and where it comes out is worked out
-- rather than chosen here. A block is emitted into the narrowest generated
-- file that every use of it can see, so a definition two files reach lands in
-- the one they both import and a definition one file reaches lands in that
-- file. What no file reaches is not emitted at all. See
-- LeanMetaReduce::placeNativeDefs.
--
-- A block runs from `-- $native <name> ...` to the next marker and is the
-- unit that is kept or dropped; the names are what it defines, and naming
-- several keeps them together. A `-- $native-needs <scope>` line opens the
-- section of blocks that need that much of the embedding in scope, which is
-- the floor on where they can be emitted:
--
--   SmtEval  nothing but Lean itself, so anywhere
--   Eo       the Eunoia term embedding, so no higher than the checker
--   Smtm     the SMT-LIB value embedding, so no higher than the model
--
-- Blocks are written in dependency order: a block may name one above it in
-- this file, never one below, since the two may come out in the same file.
-- What a block needs of the scope above it is why a section is a section.
--
-- A definition no signature may name is called `impl_native_` rather than
-- `native_`. Which of the two a name has is what says whether a signature can
-- reach it, and nothing else has to: an eoc reference names a native in
-- quotes, and the compiler answers `"X"` with `native_X`, so no reference can
-- spell an `impl_native_` name at all. What such a definition is for is the
-- one written above it, which is free to change it.

-- $native-needs SmtEval

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

-- $native native_string_lit
def native_string_lit (s : String) : native_String :=
  s.toList.map Char.toNat

-- $native impl_native_string_prefix_eq
def impl_native_string_prefix_eq : native_String -> native_String -> native_Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: cs, d :: ds => decide (c = d) && impl_native_string_prefix_eq cs ds

    -- compare a.num / a.den vs b.num / b.den by cross-multiplication

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

-- $native impl_native_int_log_rec
-- Helper for native_int_log: repeatedly divides `remaining` by `base`, counting
-- the steps until it drops below `base`. `fuel` bounds the recursion (the caller
-- passes the value itself, which is always at least the number of steps when
-- base >= 2).
def impl_native_int_log_rec (base : native_Nat) : native_Nat -> native_Nat -> native_Nat
  | 0, _ => 0
  | fuel + 1, remaining =>
    if remaining < base then 0 else 1 + impl_native_int_log_rec base fuel (remaining / base)

-- $native native_int_log
-- The (rounded-down) integer logarithm of `v` in base `b`, i.e. the greatest
-- m >= 0 such that b^m <= v, or 0 when b <= 1 or v <= 0. This aligns with Lean's
-- `Nat.log` and is the integer inverse of native_zexp_total.
def native_int_log (b : native_Int) (v : native_Int) : native_Int :=
  let base := Int.toNat b
  let value := Int.toNat v
  if base <= 1 || value == 0 then 0 else Int.ofNat (impl_native_int_log_rec base value value)

-- $native native_int_pow2
def native_int_pow2 (n : native_Int) : native_Int :=
  (native_zexp_total 2 n)

-- $native native_piand
def native_piand : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) &&& (BitVec.ofInt (Int.toNat w) y)).toInt

-- $native impl_native_pior
def impl_native_pior : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ||| (BitVec.ofInt (Int.toNat w) y)).toInt

-- $native impl_native_pixor
def impl_native_pixor : native_Int -> native_Int -> native_Int -> native_Int
  | w, x, y => ((BitVec.ofInt (Int.toNat w) x) ^^^ (BitVec.ofInt (Int.toNat w) y)).toInt

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

-- Conversions

-- $native native_to_int
def native_to_int : native_Rat -> native_Int
  | x => (Rat.floor x)

-- $native native_to_real
def native_to_real : native_Int -> native_Rat
  | x => (native_mk_rational x 1)

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
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (impl_native_pior w n1 n2))

-- $native native_binary_xor
def native_binary_xor : native_Int -> native_Int -> native_Int -> native_Int
  | w, n1, n2 => (native_ite (native_zeq w 0) 0 (impl_native_pixor w n1 n2))

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

-- $native native_nat_zero
syntax "native_nat_zero" : term
macro_rules
  | `(native_nat_zero) => `(Nat.zero)

-- $native native_nat_succ
syntax "native_nat_succ " term : term
macro_rules
  | `(native_nat_succ $x) => `(Nat.succ $x)

-- Strings of the checker. The Eunoia string operators are over Lean strings,
-- where the SMT-LIB ones are over sequences of values, so the two are
-- different functions of the layer rather than one shared by both.

-- $native native_str_len
def native_str_len : native_String -> native_Int
  | x => Int.ofNat x.length

-- $native native_str_concat
def native_str_concat : native_String -> native_String -> native_String
  | x, y => x ++ y

-- $native native_str_substr
def native_str_substr (s : native_String) (i n : native_Int) : native_String :=
  let len : Int := (native_str_len s)
  if i < 0 || n <= 0 || i >= len then
    []
  else
    let start : Nat := Int.toNat i
    let take  : Nat := Int.toNat (min n (len - i))
    (s.drop start).take take

-- $native impl_native_str_indexof_rec
def impl_native_str_indexof_rec (s t : native_String) (i fuel : Nat) : native_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if impl_native_string_prefix_eq t (s.drop i) then
        Int.ofNat i
      else
        impl_native_str_indexof_rec s t (i + 1) fuel

-- $native native_str_indexof
def native_str_indexof (s t : native_String) (i : native_Int) : native_Int :=
  if i < 0 then
    -1
  else
    let sLen := Int.toNat (native_str_len s)
    let start := Int.toNat i
    let tLen := Int.toNat (native_str_len t)
    if h : start + tLen <= sLen then
      impl_native_str_indexof_rec s t start (sLen - (start + tLen) + 1)
    else
      -1

-- What the model needs of Lean alone: arithmetic and characters it computes
-- with, the names it gives the values an ill-formed application takes, and
-- the list of references a datatype declaration is checked against.

-- $native RefList native_reflist_nil native_reflist_insert native_reflist_contains
abbrev RefList := List native_String

def native_reflist_nil : RefList := []
def native_reflist_insert (xs : RefList) (s : native_String) := (s :: xs)
def native_reflist_contains (xs : RefList) (s : native_String ) :=
  decide (s ∈ xs)

-- $native native_int_log2
def native_int_log2 : native_Int -> native_Int
  | x => Int.ofNat (Nat.log2 (Int.toNat x))

-- $native native_zabs
def native_zabs : native_Int -> native_Int
  | x => if x < 0 then -x else x

-- $native native_qabs
def native_qabs : native_Rat -> native_Rat
  | x => if x < 0 then -x else x

-- $native impl_native_char_is_digit
def impl_native_char_is_digit (c : native_Char) : native_Bool :=
  48 <= c && c <= 57

-- $native impl_native_char_to_upper
def impl_native_char_to_upper (c : native_Char) : native_Char :=
  if 97 <= c && c <= 122 then c - 32 else c

-- $native impl_native_char_to_lower
def impl_native_char_to_lower (c : native_Char) : native_Char :=
  if 65 <= c && c <= 90 then c + 32 else c

-- $native impl_native_decimal_digits_to_nat
def impl_native_decimal_digits_to_nat (xs : native_String) : native_Nat :=
  xs.foldl (fun acc c => 10 * acc + (c - 48)) 0

-- $native native_str_lt
def native_str_lt : native_String -> native_String -> native_Bool
  | s₁, s₂ => decide (s₁ < s₂)

-- $native native_str_from_int
def native_str_from_int : native_Int -> native_String
  | i => if i < 0 then native_string_lit "" else native_string_lit (toString i)

-- $native native_str_to_int
def native_str_to_int : native_String -> native_Int
  | s => match s with
          | [] => -1
          | _ => if s.all impl_native_char_is_digit then Int.ofNat (impl_native_decimal_digits_to_nat s) else -1

-- $native native_str_to_upper
def native_str_to_upper : native_String -> native_String
  | s => s.map impl_native_char_to_upper

-- $native native_str_to_lower
def native_str_to_lower : native_String -> native_String
  | s => s.map impl_native_char_to_lower

-- Partial semantics

-- $native native_qdiv_by_zero_id
def native_qdiv_by_zero_id : native_String := (native_string_lit "@qdiv_by_zero")

-- $native native_div_by_zero_id
def native_div_by_zero_id : native_String := (native_string_lit "@div_by_zero")

-- $native native_mod_by_zero_id
def native_mod_by_zero_id : native_String := (native_string_lit "@mod_by_zero")

-- $native native_wrong_apply_sel_id
def native_wrong_apply_sel_id (n m : native_Nat) : native_String :=
  (native_string_lit "@wrong_apply_sel_") ++ (native_string_lit (toString n)) ++ (native_string_lit "_") ++ (native_string_lit (toString m))

-- $native native_oob_seq_nth_id
def native_oob_seq_nth_id : native_String := (native_string_lit "@oob_seq_nth")

-- $native native_uconst_id
def native_uconst_id : native_Nat -> native_String
  | i => (native_string_lit "@u.") ++ (native_string_lit (toString i))

-- $native native_const_id
def native_const_id : native_Nat -> native_String
  | i => (native_string_lit "@c.") ++ (native_string_lit (toString i))

-- Regular expressions

-- $native native_string_head_eq
/- Whether s begins with the one character c holds. This is narrower than a
   prefix test on purpose: what a signature reserves a name by is one
   character, and the general prefix matcher stays private to this layer. -/
def native_string_head_eq (c s : native_String) : native_Bool :=
  match c, s with
  | [x], y :: _ => decide (x = y)
  | _, _ => false

-- $native-needs Eo

-- Equality, ordering and hashing of Eunoia terms, which the checker asks of
-- the layer because the term embedding is what it decides them over.

-- $native native_teq
/- Term equality -/
def native_teq : Term -> Term -> native_Bool
  | x, y => decide (x = y)

-- $native native_tcmp
/- Term less than, based on arbitrary ordering -/
def native_tcmp (a b : Term) : native_Bool :=
  match compare a b with
  | Ordering.lt => true
  | _ => false

-- $native-needs Smtm

-- The reference lists are not reached by any signature compiled so far: they
-- are for the translation proofs of the package the published tree is
-- installed into, which this compiler never sees. So they are roots rather
-- than definitions the compilation has to reach.

-- $native native_Teq
/- Type equality -/
def native_Teq : SmtType -> SmtType -> native_Bool
  | x, y => decide (x = y)

-- $native native_veq
/- Value equality -/
def native_veq : SmtValue -> SmtValue -> native_Bool
  | x, y => decide (x = y)

-- $native native_vcmp
/- Value comparsion -/
def native_vcmp (v1 : SmtValue) (v2 : SmtValue) : native_Bool :=
  SmtValueOrder.lt v1 v2

-- SMT Beyond Eunoia

-- $native native_re_elem_valid
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

-- $native impl_native_re_elem_le
/-- Character ordering on base elements; only characters are comparable. -/
def impl_native_re_elem_le : SmtValue -> SmtValue -> native_Bool
  | (SmtValue.Char c₁), (SmtValue.Char c₂) => c₁ <= c₂
  | _, _ => false

-- $native impl_native_string_to_values
/-- The embedding of native strings as value sequences. -/
def impl_native_string_to_values (s : native_String) : List SmtValue :=
  s.map SmtValue.Char

-- $native impl_native_re_str_valid
/-- Whether a value sequence denotes a valid string, i.e. all of its
elements are valid character values. -/
def impl_native_re_str_valid (xs : List SmtValue) : native_Bool :=
  xs.all native_re_elem_valid

-- $native impl_native_re_nullable
def impl_native_re_nullable : SmtRegLan -> native_Bool
  | .empty => false
  | .epsilon => true
  | .char _ => false
  | .range _ _ => false
  | .allchar => false
  | .concat r₁ r₂ => impl_native_re_nullable r₁ && impl_native_re_nullable r₂
  | .union r₁ r₂ => impl_native_re_nullable r₁ || impl_native_re_nullable r₂
  | .inter r₁ r₂ => impl_native_re_nullable r₁ && impl_native_re_nullable r₂
  | .star _ => true
  | .comp r => !(impl_native_re_nullable r)

-- $native native_re_concat
def native_re_concat (r₁ r₂ : SmtRegLan) : SmtRegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r₁, r₂ => .concat r₁ r₂

-- $native native_re_union
def native_re_union (r₁ r₂ : SmtRegLan) : SmtRegLan :=
  match r₁, r₂ with
  | .empty, r => r
  | r, .empty => r
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .union r₁ r₂

-- $native native_re_inter
def native_re_inter (r₁ r₂ : SmtRegLan) : SmtRegLan :=
  match r₁, r₂ with
  | .empty, _ => .empty
  | _, .empty => .empty
  | r₁, r₂ => if h : r₁ = r₂ then r₁ else .inter r₁ r₂

-- $native native_re_comp
def native_re_comp : SmtRegLan -> SmtRegLan
  | .comp r => r
  | r => .comp r

-- $native native_re_mult
def native_re_mult : SmtRegLan -> SmtRegLan
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

-- $native impl_native_re_deriv
def impl_native_re_deriv (c : SmtValue) : SmtRegLan -> SmtRegLan
  | .empty => .empty
  | .epsilon => .empty
  | .char d => if c = d then .epsilon else .empty
  | .range lo hi =>
      if native_re_elem_valid c && native_re_elem_valid lo && native_re_elem_valid hi
          && impl_native_re_elem_le lo c && impl_native_re_elem_le c hi then
        .epsilon
      else
        .empty
  | .allchar => if native_re_elem_valid c then .epsilon else .empty
  | .concat r₁ r₂ =>
      native_re_union
        (native_re_concat (impl_native_re_deriv c r₁) r₂)
        (if impl_native_re_nullable r₁ then impl_native_re_deriv c r₂ else .empty)
  | .union r₁ r₂ => native_re_union (impl_native_re_deriv c r₁) (impl_native_re_deriv c r₂)
  | .inter r₁ r₂ => native_re_inter (impl_native_re_deriv c r₁) (impl_native_re_deriv c r₂)
  | .star r => native_re_concat (impl_native_re_deriv c r) (.star r)
  | .comp r => native_re_comp (impl_native_re_deriv c r)

-- $native impl_native_re_of_list
def impl_native_re_of_list : List SmtValue -> SmtRegLan
  | [] => .epsilon
  | c :: cs => native_re_concat (.char c) (impl_native_re_of_list cs)

-- $native impl_native_re_prefix_match_len? impl_native_re_prefix_match_len?.go
def impl_native_re_prefix_match_len?.go (r : SmtRegLan) :
    List SmtValue → Nat → Option Nat
  | [], n =>
      if impl_native_re_nullable r then some n else none
  | c :: cs, n =>
      if impl_native_re_nullable r then
        some n
      else
        impl_native_re_prefix_match_len?.go (impl_native_re_deriv c r) cs (n + 1)

def impl_native_re_prefix_match_len? (r : SmtRegLan)
    (xs : List SmtValue) : Option Nat :=
  impl_native_re_prefix_match_len?.go r xs 0

-- $native impl_native_re_positive_prefix_match_len?
def impl_native_re_positive_prefix_match_len? (r : SmtRegLan) :
    List SmtValue -> Option Nat
  | [] => none
  | c :: cs =>
      match impl_native_re_prefix_match_len? (impl_native_re_deriv c r) cs with
      | some n => some (n + 1)
      | none => none

-- $native impl_native_re_find_idx_aux
def impl_native_re_find_idx_aux (r : SmtRegLan) (xs : List SmtValue) (idx : Nat) : Option (Nat × Nat) :=
  match impl_native_re_prefix_match_len? r xs with
  | some n => some (idx, n)
  | none =>
      match xs with
      | [] => none
      | _ :: cs => impl_native_re_find_idx_aux r cs (idx + 1)

-- $native impl_native_re_find_idx_from
def impl_native_re_find_idx_from (r : SmtRegLan) (xs : List SmtValue) (start : Nat) : Option (Nat × Nat) :=
  impl_native_re_find_idx_aux r (xs.drop start) start

-- $native impl_native_re_find_nonempty_idx_aux
def impl_native_re_find_nonempty_idx_aux (r : SmtRegLan) (xs : List SmtValue) (idx : Nat) :
    Option (Nat × Nat) :=
  match impl_native_re_positive_prefix_match_len? r xs with
  | some (n + 1) => some (idx, n + 1)
  | _ =>
      match xs with
      | [] => none
      | _ :: cs => impl_native_re_find_nonempty_idx_aux r cs (idx + 1)

-- $native impl_native_re_find_nonempty_idx_from
def impl_native_re_find_nonempty_idx_from (r : SmtRegLan) (xs : List SmtValue) (start : Nat) :
    Option (Nat × Nat) :=
  impl_native_re_find_nonempty_idx_aux r (xs.drop start) start

-- $native impl_native_re_replace_all_nonempty_list_aux
def impl_native_re_replace_all_nonempty_list_aux (fuel : Nat) (r : SmtRegLan)
    (replacement : List SmtValue) : List SmtValue -> List SmtValue
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match impl_native_re_positive_prefix_match_len? r xs with
          | some (n + 1) =>
              replacement ++ impl_native_re_replace_all_nonempty_list_aux fuel r replacement
                (xs.drop (n + 1))
          | _ =>
              match xs with
              | [] => []
              | c :: cs => c :: impl_native_re_replace_all_nonempty_list_aux fuel r replacement cs

-- $native impl_native_re_replace_all_nonempty_list
def impl_native_re_replace_all_nonempty_list (r : SmtRegLan) (replacement xs : List SmtValue) :
    List SmtValue :=
  impl_native_re_replace_all_nonempty_list_aux (xs.length + 1) r replacement xs

-- $native native_str_to_re
def native_str_to_re : List SmtValue -> SmtRegLan
  | s => impl_native_re_of_list s

-- $native native_re_diff
def native_re_diff : SmtRegLan -> SmtRegLan -> SmtRegLan
  | r₁, r₂ => native_re_inter r₁ (native_re_comp r₂)

-- $native native_re_range
def native_re_range : List SmtValue -> List SmtValue -> SmtRegLan
  | s₁, s₂ =>
      match s₁, s₂ with
      | [v₁], [v₂] => .range v₁ v₂
      | _, _ => .empty

-- $native native_str_in_re
def native_str_in_re : List SmtValue -> SmtRegLan -> native_Bool
  | s, r =>
      if impl_native_re_str_valid s then
        impl_native_re_nullable <| s.foldl (fun acc c => impl_native_re_deriv c acc) r
      else
        false

-- $native native_str_indexof_re
def native_str_indexof_re : List SmtValue -> SmtRegLan -> native_Int -> native_Int
  | s, r, i =>
      if i < 0 then
        -1
      else
        let start := Int.toNat i
        if start <= s.length then
          match impl_native_re_find_idx_from r s start with
          | some (idx, _) => Int.ofNat idx
          | none => -1
        else
          -1

-- $native impl_native_str_indexof_re_split_aux
/-- Searches for the smallest split point of `s` into a prefix matching `r1` and a
suffix matching `r2`.  `pre` is the prefix consumed so far (i.e. `s` with `suf`
dropped) and `i` its length; recursion is structural on the remaining suffix. -/
def impl_native_str_indexof_re_split_aux (r1 r2 : SmtRegLan) :
    List SmtValue -> List SmtValue -> native_Nat -> native_Int
  | pre, suf, i =>
      if native_str_in_re pre r1 && native_str_in_re suf r2 then
        Int.ofNat i
      else
        match suf with
        | [] => -1
        | c :: cs => impl_native_str_indexof_re_split_aux r1 r2 (pre ++ [c]) cs (i + 1)

-- $native native_str_indexof_re_split
def native_str_indexof_re_split : List SmtValue -> SmtRegLan -> SmtRegLan -> native_Int
  | s, r1, r2 =>
      if impl_native_re_str_valid s then
        impl_native_str_indexof_re_split_aux r1 r2 [] s 0
      else
        -1

-- $native native_str_replace_re
def native_str_replace_re : List SmtValue -> SmtRegLan -> List SmtValue -> List SmtValue
  | s, r, replacement =>
      match impl_native_re_find_idx_from r s 0 with
      | some (idx, len) =>
          (s.take idx) ++ replacement ++ (s.drop (idx + len))
      | none => s

-- $native native_str_replace_re_all
def native_str_replace_re_all : List SmtValue -> SmtRegLan -> List SmtValue -> List SmtValue
  | s, r, replacement =>
      impl_native_re_replace_all_nonempty_list r replacement s

-- $native impl_native_re_scan_ends_aux
/-- End positions of the nonempty-match scan used by `str.replace_re_all`:
successive leftmost, shortest, nonempty matches of `r` in `s` at or after
`pos`.  Each step consumes at least one character, so `s.length + 1` fuel is
always sufficient. -/
def impl_native_re_scan_ends_aux (fuel : Nat) (r : SmtRegLan) (s : List SmtValue) :
    Nat -> List Nat
  | pos =>
      match fuel with
      | 0 => []
      | fuel + 1 =>
          match impl_native_re_find_nonempty_idx_from r s pos with
          | some (idx, len) =>
              (idx + len) :: impl_native_re_scan_ends_aux fuel r s (idx + len)
          | none => []

-- $native native_str_occur_index_re
/-- The `n`-th boundary of the nonempty-match scan of `r` over `s`: `0` for
`n = 0`, the end position of the `n`-th match for `1 <= n <=` the number of
matches, and `-1` out of range. The sequence occurrence-index operator is
evaluated by this operator via a singleton regular expression over its
pattern. -/
def native_str_occur_index_re (s : List SmtValue) (r : SmtRegLan) (n : native_Int) : native_Int :=
  let bnds := 0 :: impl_native_re_scan_ends_aux (s.length + 1) r s 0
  if 0 ≤ n ∧ Int.toNat n < bnds.length then
    Int.ofNat (bnds.getD (Int.toNat n) 0)
  else
    -1

-- $native native_re_allchar
def native_re_allchar : SmtRegLan := .allchar

-- $native native_re_none
def native_re_none : SmtRegLan := .empty

-- $native native_re_all
def native_re_all : SmtRegLan := .star .allchar

-- $native native_re_canonical
def native_re_canonical : SmtRegLan -> native_Bool
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

-- $native native_re_ext_eq
macro_rules
  | `(native_re_ext_eq $r1 $r2) => do
      let strInReId := Lean.mkIdent `native_str_in_re
      let validId := Lean.mkIdent `native_string_valid
      let toValuesId := Lean.mkIdent `impl_native_string_to_values
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

-- $native native_eval_map_diff_msm
macro_rules
  | `(native_eval_map_diff_msm $m1 $m2) => do
      let lookupId := Lean.mkIdent `__smtx_map_lookup
      let typeofMapValueId := Lean.mkIdent `__smtx_typeof_map_value
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      let typeDefaultId := Lean.mkIdent `__smtx_type_default
      let canonId := Lean.mkIdent `__smtx_value_canonical
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

-- $native native_eval_seq_diff_ssm
macro_rules
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
