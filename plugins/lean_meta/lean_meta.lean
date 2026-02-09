
namespace Eo

/- Builtin data types, placeholders -/

constant smt_Bool : Type
constant smt_Int : Type
constant smt_Real : Type
constant smt_String : Type

/- Evaluation functions, placeholders -/

constant smt_not : smt_Bool -> smt_Bool
constant smt_and : smt_Bool -> smt_Bool -> smt_Bool
constant smt_or : smt_Bool -> smt_Bool -> smt_Bool
constant smt_xor : smt_Bool -> smt_Bool -> smt_Bool

constant smt_= : forall (T : Type), T -> T -> smt_Bool
constant smt_ite : forall (T : Type), smt_Bool -> T -> T -> T

constant smt_+ : forall (T : Type), T -> T -> T
constant smt_* : forall (T : Type), T -> T -> T
constant smt_/ : forall (T : Type), T -> T -> smt_Real
constant smt_div : smt_Int -> smt_Int -> smt_Int
constant smt_mod : smt_Int -> smt_Int -> smt_Int
constant smt_<= : forall (T : Type), T -> T -> smt_Bool
constant smt_to_int : forall (T : Type), T -> smt_Int
constant smt_to_real : forall (T : Type), T -> smt_Real

constant smt_str.len : smt_String -> smt_Int
constant smt_str.++ : smt_String -> smt_String -> smt_String
constant smt_str.substr : smt_String -> smt_Int -> smt_Int -> smt_String
constant smt_str.indexof : smt_String -> smt_String -> smt_Int -> smt_Int
constant smt_str.to_code : smt_String -> smt_Int
constant smt_str.from_code : smt_Int -> smt_String

/- Term definition -/

inductive Term : Type where
$LEAN_TERM_DEF$

/- Relevant definitions -/

$LEAN_DEFS$

/- The verification conditions -/

$LEAN_THMS$

end Eo
