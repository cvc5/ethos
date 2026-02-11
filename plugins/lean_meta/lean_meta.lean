
namespace Eo

/- Placeholder for SMT-LIB semantics -/

/-
An SMT-LIB term. This is a placeholder for the definition of SMT-LIB terms.
This is to be defined externally.
-/
inductive Smt_Term : Type where
  | Id : String -> Smt_Term
  | Apply : Smt_Term -> Smt_Term -> Smt_Term

/-
A predicate defining a relation on SMT-LIB terms and Booleans such that
(s,b) is true if the SMT term s evaluates to b in the standard model.
This is to be defined externally.
-/
axiom smt_interprets : Smt_Term -> Bool -> Prop

/- Builtin data types -/

abbrev eo_lit_Bool := Bool
abbrev eo_lit_Int := Int
abbrev eo_lit_Real := Rat
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
def eo_lit_mk_rational : eo_lit_Int -> eo_lit_Int -> eo_lit_Real
  | x, y => x/y
def eo_lit_qplus : eo_lit_Real -> eo_lit_Real -> eo_lit_Real
  | x, y => x+y
def eo_lit_qmult : eo_lit_Real -> eo_lit_Real -> eo_lit_Real
  | x, y => x*y
def eo_lit_qneg : eo_lit_Real -> eo_lit_Real
  | x => -x
def eo_lit_qleq : eo_lit_Real -> eo_lit_Real -> eo_lit_Bool
  | x, y => decide (x <= y)
def eo_lit_qlt : eo_lit_Real -> eo_lit_Real -> eo_lit_Bool
  | x, y => decide (x < y)
def eo_lit_qdiv : eo_lit_Real -> eo_lit_Real -> eo_lit_Real
  | x, y => x/y
  
-- Conversions
def eo_lit_to_int : eo_lit_Real -> eo_lit_Int
  | x => 0 -- FIXME
def eo_lit_to_real : eo_lit_Int -> eo_lit_Real
  | x => (eo_lit_mk_rational x 1)

-- Strings
def eo_lit_str_len : eo_lit_String -> eo_lit_Int
  | x => Int.ofNat x.length
def eo_lit_str_concat : eo_lit_String -> eo_lit_String -> eo_lit_String
  | x, y => x ++ y
def eo_lit_str_substr : eo_lit_String -> eo_lit_Int -> eo_lit_Int -> eo_lit_String
  | _, _, _ => "" -- FIXME
def eo_lit_str_indexof : eo_lit_String -> eo_lit_String -> eo_lit_Int -> eo_lit_Int
  | _, _, _ => 0 -- FIXME
def eo_lit_str_to_code : eo_lit_String -> eo_lit_Int
  | _ => 0 -- FIXME
def eo_lit_str_from_code : eo_lit_Int -> eo_lit_String
  | _ => "" -- FIXME

/- Term definition -/

inductive Term : Type where
$LEAN_TERM_DEF$
deriving DecidableEq

/- Term equality -/
def eo_lit_eq : Term -> Term -> eo_lit_Bool
  | x, y => decide (x = y)
  
/- Relevant definitions -/

mutual

$LEAN_DEFS$

end 

/- The theorem statements -/

/-
An inductive predicate defining the correspondence between Eunoia terms
and SMT-LIB terms.
(t,s) is true if the Eunoia term represents SMT-LIB term s.
-/
inductive eo_is_smt : Term -> Model_Term -> Prop
$LEAN_EO_IS_SMT_DEF$

/-
A predicate defining when a Eunoia term corresponds to an SMT-LIB term that
evaluates to true or false in a model.
(t,b) is true if t is a Eunoia term corresponding to an SMT-LIB term that
evaluates to b in the standard model.
-/
def eo_interprets (t : Term) (b : Bool) : Prop :=
  exists (s : Smt_Term), (eo_is_smt t s) /\ (smt_interprets s b)

$LEAN_THMS$

end Eo
