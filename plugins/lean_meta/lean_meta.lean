
namespace Eo

/- 
Placeholder for SMT-LIB terms.
TODO: define this separately
-/
inductive Smt_Term : Type where
  | Boolean : Bool -> Smt_Term
  | Numeral : Int -> Smt_Term
  | Rational : Rat -> Smt_Term
  | String : String -> Smt_Term
  | Binary : Int -> Int -> Smt_Term
  | Id : String -> Smt_Term
  | Apply : Smt_Term -> Smt_Term -> Smt_Term

/-
A definition of terms in the object language.
This is to be defined externally.
-/
abbrev Object_Term := Smt_Term

/-
A predicate defining a relation on terms in the object language and Booleans
such that (s,b) is true if s evaluates to b.
This is to be defined externally.
-/
axiom obj_interprets : Object_Term -> Bool -> Prop

/- Builtin data types -/

abbrev eo_lit_Bool := Bool
abbrev eo_lit_Int := Int
abbrev eo_lit_Rat := Rat
abbrev eo_lit_String := String

/- Evaluation functions -/

def eo_lit_not : eo_lit_Bool -> eo_lit_Bool
  | x => Bool.not x
def eo_lit_and : eo_lit_Bool -> eo_lit_Bool -> eo_lit_Bool
  | x, y => x && y
def eo_lit_or : eo_lit_Bool -> eo_lit_Bool -> eo_lit_Bool
  | x, y => x || y
def eo_lit_xor : eo_lit_Bool -> eo_lit_Bool -> eo_lit_Bool
  | x, y => Bool.xor x y

def eo_lit_ite {T : Type} (c : Bool) (t e : T) : T :=
  if c then t else e

-- Integer arithmetic
def eo_lit_zplus : eo_lit_Int -> eo_lit_Int -> eo_lit_Int
  | x, y => x+y
def eo_lit_zmult : eo_lit_Int -> eo_lit_Int -> eo_lit_Int
  | x, y => x*y
def eo_lit_zneg : eo_lit_Int -> eo_lit_Int
  | x => -x
def eo_lit_zleq : eo_lit_Int -> eo_lit_Int -> eo_lit_Bool
  | x, y => decide (x <= y)
def eo_lit_zlt : eo_lit_Int -> eo_lit_Int -> eo_lit_Bool
  | x, y => decide (x < y)
def eo_lit_div : eo_lit_Int -> eo_lit_Int -> eo_lit_Int
  | x, y => x/y
def eo_lit_mod : eo_lit_Int -> eo_lit_Int -> eo_lit_Int
  | x, y => x%y
  
-- Rational arithmetic
def eo_lit_mk_rational : eo_lit_Int -> eo_lit_Int -> eo_lit_Rat
  | x, y => x/y
def eo_lit_qplus : eo_lit_Rat -> eo_lit_Rat -> eo_lit_Rat
  | x, y => x+y
def eo_lit_qmult : eo_lit_Rat -> eo_lit_Rat -> eo_lit_Rat
  | x, y => x*y
def eo_lit_qneg : eo_lit_Rat -> eo_lit_Rat
  | x => -x
def eo_lit_qleq : eo_lit_Rat -> eo_lit_Rat -> eo_lit_Bool
  | x, y => decide (x <= y)
def eo_lit_qlt : eo_lit_Rat -> eo_lit_Rat -> eo_lit_Bool
  | x, y => decide (x < y)
def eo_lit_qdiv : eo_lit_Rat -> eo_lit_Rat -> eo_lit_Rat
  | x, y => x/y
  
-- Conversions
def eo_lit_to_int : eo_lit_Rat -> eo_lit_Int
  | x => (Rat.floor x)
def eo_lit_to_real : eo_lit_Int -> eo_lit_Rat
  | x => (eo_lit_mk_rational x 1)

-- Strings
def eo_lit_str_len : eo_lit_String -> eo_lit_Int
  | x => Int.ofNat x.length
def eo_lit_str_concat : eo_lit_String -> eo_lit_String -> eo_lit_String
  | x, y => x ++ y
def eo_lit_str_substr (s : eo_lit_String) (i n : eo_lit_Int) : eo_lit_String :=
  let len : Int := (eo_lit_str_len s)
  if i < 0 || n <= 0 || i >= len then
    ""
  else
    let start : Nat := Int.toNat i
    let take  : Nat := Int.toNat (min n (len - i))
    String.Pos.Raw.extract s ⟨start⟩ ⟨start + take⟩
def eo_lit_str_indexof_rec (s t : eo_lit_String) (i len : Nat) : eo_lit_Int :=
  if (i+len)>(eo_lit_str_len s) then
    -1
  else if String.Pos.Raw.substrEq s ⟨i⟩ t ⟨0⟩ len then
    i
  else 
    eo_lit_str_indexof_rec s t (i+1) len
decreasing_by sorry  -- FIXME
def eo_lit_str_indexof (s t : eo_lit_String) (i : eo_lit_Int) : eo_lit_Int :=
  if i < 0 then
    -1
  else
    (eo_lit_str_indexof_rec s t (Int.toNat i) (Int.toNat (eo_lit_str_len t)))
def eo_lit_str_to_code (s : eo_lit_String) : eo_lit_Int :=
  match s.toList with
  | [c] => Int.ofNat c.toNat
  | _   => -1
def eo_lit_str_from_code (i : eo_lit_Int) : eo_lit_String :=
  if (0 <= i && i <= 196608) then
    String.singleton (Char.ofNat (Int.toNat i))
  else
    ""

/- Term definition -/

inductive Term : Type where
$LEAN_TERM_DEF$
deriving DecidableEq
  
/- Term equality -/
def eo_lit_eq : Term -> Term -> eo_lit_Bool
  | x, y => decide (x = y)

/- Used for defining hash -/
def __smtx_hash : Term -> eo_lit_Int
  | _ => 0 -- FIXME

/- Proofs -/
inductive Proof : Type where
  | pf : Term -> Proof
  
/- Relevant definitions -/

mutual

$LEAN_DEFS$

end 

/- Definitions for theorems -/

/-
An inductive predicate defining the correspondence between Eunoia terms
and terms in the object language.
(t,s) is true if the Eunoia term represents a term s in the object language.
This is to be custom defined in the Eunoia-to-Lean compiler based on the
target definition of Object_Term.
-/
inductive eo_is_obj : Term -> Object_Term -> Prop
$LEAN_EO_IS_OBJ_DEF$

/-
A predicate defining when a Eunoia term corresponds to an object term that
evaluates to true or false.
(t,b) is true if t is a Eunoia term corresponding to an object term that
evaluates to b.
-/
def eo_interprets (t : Term) (b : Bool) : Prop :=
  exists (s : Object_Term), (eo_is_obj t s) /\ (obj_interprets s b)

/- The theorem statements -/

$LEAN_THMS$

end Eo
