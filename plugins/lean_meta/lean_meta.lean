
namespace Eo


/- Builtin data types, placeholders -/

inductive smt_Bool : Type where
  | id : smt_Bool
  | true : smt_Bool
  | false : smt_Bool
inductive smt_Int : Type where
  | id : smt_Int
inductive smt_Real : Type where
  | id : smt_Real
inductive smt_String : Type where
  | id : smt_String

/- Evaluation functions, placeholders -/

def smt_not : smt_Bool -> smt_Bool
  | _ => smt_Bool.id
def smt_and : smt_Bool -> smt_Bool -> smt_Bool
  | _, _ => smt_Bool.id
def smt_or : smt_Bool -> smt_Bool -> smt_Bool
  | _, _ => smt_Bool.id
def smt_xor : smt_Bool -> smt_Bool -> smt_Bool
  | _, _ => smt_Bool.id

def smt_eq : forall {T : Type}, T -> T -> smt_Bool
  | _, _, _ => smt_Bool.id
def smt_ite : forall {T : Type}, smt_Bool -> T -> T -> T
  | _, _, x, _ => x

def smt_plus : forall {T : Type}, T -> T -> T
  | _, x, _ => x
def smt_mult : forall {T : Type}, T -> T -> T
  | _, x, _ => x
def smt_neg : forall {T : Type}, T -> T
  | _, x => x
def smt_qdiv : forall {T : Type}, T -> T -> smt_Real
  | _, _, _ => smt_Real.id
def smt_div : smt_Int -> smt_Int -> smt_Int
  | _, _ => smt_Int.id
def smt_mod : smt_Int -> smt_Int -> smt_Int
  | _, _ => smt_Int.id
def smt_leq : forall {T : Type}, T -> T -> smt_Bool
  | _, _, _ => smt_Bool.id
def smt_to_int : forall {T : Type}, T -> smt_Int
  | _, _ => smt_Int.id
def smt_to_real : forall {T : Type}, T -> smt_Real
  | _, _ => smt_Real.id

def smt_str_len : smt_String -> smt_Int
  | _ => smt_Int.id
def smt_str_concat : smt_String -> smt_String -> smt_String
  | _, _ => smt_String.id
def smt_str_substr : smt_String -> smt_Int -> smt_Int -> smt_String
  | _, _, _ => smt_String.id
def smt_str_indexof : smt_String -> smt_String -> smt_Int -> smt_Int
  | _, _, _ => smt_Int.id
def smt_str_to_code : smt_String -> smt_Int
  | _ => smt_Int.id
def smt_str_from_code : smt_Int -> smt_String
  | _ => smt_String.id

/- Term definition -/

inductive Term : Type where
$LEAN_TERM_DEF$

/- Relevant definitions -/

mutual

$LEAN_DEFS$

end 

/- The verification conditions -/

axiom eo_model_Bool : Term -> smt_Bool -> Prop

$LEAN_THMS$

end Eo
