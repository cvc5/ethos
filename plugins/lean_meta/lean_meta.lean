
namespace Eo


/- Builtin data types, placeholders -/

abbrev smt_Bool := Bool
abbrev smt_Int := Int
abbrev smt_Real := Rat
inductive smt_String : Type where
  | id : smt_String
deriving DecidableEq

/- Evaluation functions, placeholders -/

def smt_not : smt_Bool -> smt_Bool
  | x => Bool.not x
def smt_and : smt_Bool -> smt_Bool -> smt_Bool
  | x, y => x && y
def smt_or : smt_Bool -> smt_Bool -> smt_Bool
  | x, y => x || y
def smt_xor : smt_Bool -> smt_Bool -> smt_Bool
  | x, y => Bool.xor x y

def smt_ite : forall {T : Type}, smt_Bool -> T -> T -> T
  | _, true, x, _ => x
  | _, false, _, y => y

-- Integer arithmetic
def smt_zplus : smt_Int -> smt_Int -> smt_Int
  | x, y => x+y
def smt_zmult : smt_Int -> smt_Int -> smt_Int
  | x, y => x*y
def smt_zneg : smt_Int -> smt_Int
  | x => -x
def smt_zleq : smt_Int -> smt_Int -> smt_Bool
  | x, y => decide (x <= y)
def smt_zlt : smt_Int -> smt_Int -> smt_Bool
  | x, y => decide (x < y)
def smt_div : smt_Int -> smt_Int -> smt_Int
  | x, y => x/y
def smt_mod : smt_Int -> smt_Int -> smt_Int
  | x, y => x%y
  
-- Rational arithmetic
def smt_mk_rational : smt_Int -> smt_Int -> smt_Real
  | x, y => x/y
def smt_qplus : smt_Real -> smt_Real -> smt_Real
  | x, y => x+y
def smt_qmult : smt_Real -> smt_Real -> smt_Real
  | x, y => x*y
def smt_qneg : smt_Real -> smt_Real
  | x => -x
def smt_qleq : smt_Real -> smt_Real -> smt_Bool
  | x, y => decide (x <= y)
def smt_qlt : smt_Real -> smt_Real -> smt_Bool
  | x, y => decide (x < y)
def smt_qdiv : smt_Real -> smt_Real -> smt_Real
  | x, y => x/y
  
-- Conversions
def smt_to_int : smt_Real -> smt_Int
  | x => 0 -- FIXME
def smt_to_real : smt_Int -> smt_Real
  | x => x/1

-- Strings
def smt_str_len : smt_String -> smt_Int
  | _ => 0 -- FIXME
def smt_str_concat : smt_String -> smt_String -> smt_String
  | _, _ => smt_String.id
def smt_str_substr : smt_String -> smt_Int -> smt_Int -> smt_String
  | _, _, _ => smt_String.id
def smt_str_indexof : smt_String -> smt_String -> smt_Int -> smt_Int
  | _, _, _ => 0 -- FIXME
def smt_str_to_code : smt_String -> smt_Int
  | _ => 0 -- FIXME
def smt_str_from_code : smt_Int -> smt_String
  | _ => smt_String.id -- FIXME

/- Term definition -/

inductive Term : Type where
$LEAN_TERM_DEF$
deriving DecidableEq

/- Term equality -/
def smt_eq : Term -> Term -> smt_Bool
  | x, y => decide (x = y)
  
/- Relevant definitions -/

mutual

$LEAN_DEFS$

end 

/- The verification conditions -/

axiom eo_model_Bool : Term -> smt_Bool -> Prop

$LEAN_THMS$

end Eo
