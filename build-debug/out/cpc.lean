set_option linter.unusedVariables false

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
def eo_lit_zeq : eo_lit_Int -> eo_lit_Int -> eo_lit_Bool
  | x, y => decide (x = y)
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
def eo_lit_qeq : eo_lit_Rat -> eo_lit_Rat -> eo_lit_Bool
  | x, y => decide (x = y)
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
  | __eo_Proof : Term
  | __eo_pf : Term -> Term
  | Int : Term
  | Real : Term
  | BitVec : Term
  | Char : Term
  | Seq : Term
  | __eo_List : Term
  | __eo_List_nil : Term
  | __eo_List_cons : Term
  | Bool : Term
  | Boolean : eo_lit_Bool -> Term
  | Numeral : eo_lit_Int -> Term
  | Rational : eo_lit_Rat -> Term
  | String : eo_lit_String -> Term
  | Binary : eo_lit_Int -> eo_lit_Int -> Term
  | Type : Term
  | Stuck : Term
  | Apply : Term -> Term -> Term
  | FunType : Term
  | Var : eo_lit_String -> Term -> Term
  | not : Term
  | and : Term
  | eq : Term

deriving DecidableEq
  
/- Term equality -/
def eo_lit_teq : Term -> Term -> eo_lit_Bool
  | x, y => decide (x = y)

/- Used for defining hash -/
def __smtx_hash : Term -> eo_lit_Int
  | _ => 0 -- FIXME

/- Proofs -/
inductive Proof : Type where
  | pf : Term -> Proof
  | Stuck : Proof
  
/- Relevant definitions -/

mutual

def __eo_proven : Proof -> Term
  | (Proof.pf F) => F
  | _ => Term.Stuck


def __eo_Bool : Term := Term.Bool
def __eo_bool : eo_lit_Bool -> Term
  | x => (Term.Boolean x)


def __eo_numeral : eo_lit_Int -> Term
  | x => (Term.Numeral x)


def __eo_rational : eo_lit_Rat -> Term
  | x => (Term.Rational x)


def __eo_string : eo_lit_String -> Term
  | x => (Term.String x)


def __eo_binary : eo_lit_Int -> eo_lit_Int -> Term
  | w, v => (Term.Binary w v)


def __eo_Type : Term := Term.Type
def __eo_stuck : Term := Term.Stuck
def __eo_apply : Term -> Term -> Term
  | x, y => (Term.Apply x y)


def __eo_fun_type : Term := Term.FunType
def __eo_Var : eo_lit_String -> Term -> Term
  | s, T => (Term.Var s T)


def __eo_is_ok : Term -> Term
  | x => (Term.Boolean (eo_lit_not (eo_lit_teq x Term.Stuck)))


def __eo_ite : Term -> Term -> Term -> Term
  | x1, x2, x3 => (eo_lit_ite (eo_lit_teq x1 (Term.Boolean true)) x2 (eo_lit_ite (eo_lit_teq x1 (Term.Boolean false)) x3 Term.Stuck))


def __eo_requires : Term -> Term -> Term -> Term
  | x1, x2, x3 => (eo_lit_ite (eo_lit_teq x1 x2) (eo_lit_ite (eo_lit_not (eo_lit_teq x1 Term.Stuck)) x3 Term.Stuck) Term.Stuck)


def __eo_mk_apply : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, x2 => (Term.Apply x1 x2)


def __eo_len : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.String s1) => (Term.Numeral (eo_lit_str_len s1))
  | (Term.Binary w n1) => (Term.Numeral w)
  | _ => Term.Stuck


def __eo_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Boolean (eo_lit_teq s t))


def __eo_typeof : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Boolean b) => Term.Bool
  | (Term.Numeral n) => (__eo_lit_type_Numeral (Term.Numeral n))
  | (Term.Rational r) => (__eo_lit_type_Rational (Term.Rational r))
  | (Term.String s) => (__eo_lit_type_String (Term.String s))
  | (Term.Binary w n) => (__eo_lit_type_Binary (Term.Binary w n))
  | (Term.Var s T) => T
  | t => (__eo_typeof_main t)


def __mk_symm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq t1) t2) => (Term.Apply (Term.Apply Term.eq t2) t1)
  | (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) t2)) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t2) t1))
  | _ => Term.Stuck


def __eo_prog_symm : Proof -> Term
  | (Proof.pf F) => (__mk_symm F)
  | _ => Term.Stuck


def __eo_typeof_apply : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.FunType T) U), V => (__eo_requires T V U)
  | _, _ => Term.Stuck


def __eo_typeof_eq : Term -> Term
  | Term.Stuck  => Term.Stuck
  | A => (Term.Apply (Term.Apply Term.FunType A) Term.Bool)


def __eo_typeof_fun_type : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | Term.Type, Term.Type => Term.Type
  | _, _ => Term.Stuck


def __eo_typeof_main : Term -> Term
  | Term.Stuck  => Term.Stuck
  | Term.Type => Term.Type
  | (Term.Apply (Term.Apply Term.FunType __eo_T) __eo_U) => (__eo_typeof_fun_type (__eo_typeof __eo_T) (__eo_typeof __eo_U))
  | Term.Bool => Term.Type
  | (Term.Boolean true) => Term.Bool
  | (Term.Boolean false) => Term.Bool
  | Term.__eo_List => Term.Type
  | Term.__eo_List_nil => Term.__eo_List
  | (Term.Apply Term.__eo_List_cons __eo_x1) => (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
  | Term.Int => Term.Type
  | Term.Real => Term.Type
  | Term.BitVec => (Term.Apply (Term.Apply Term.FunType Term.Int) Term.Type)
  | Term.Char => Term.Type
  | Term.Seq => (Term.Apply (Term.Apply Term.FunType Term.Type) Term.Type)
  | Term.not => (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool)
  | Term.and => (Term.Apply (Term.Apply Term.FunType Term.Bool) (Term.Apply (Term.Apply Term.FunType Term.Bool) Term.Bool))
  | (Term.Apply Term.eq __eo_x1) => (__eo_typeof_eq (__eo_typeof __eo_x1))
  | (Term.Apply __eo_f __eo_x) => (__eo_typeof_apply (__eo_typeof __eo_f) (__eo_typeof __eo_x))
  | _ => Term.Stuck


def __eo_lit_type_Numeral : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => Term.Int


def __eo_lit_type_Rational : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => Term.Real


def __eo_lit_type_Binary : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => (__eo_mk_apply Term.BitVec (__eo_len t))


def __eo_lit_type_String : Term -> Term
  | Term.Stuck  => Term.Stuck
  | t => (Term.Apply Term.Seq Term.Char)


def __eo_dt_constructors : Term -> Term
  | Term.Stuck  => Term.Stuck
  | _ => Term.Stuck


def __eo_dt_selectors : Term -> Term
  | Term.Stuck  => Term.Stuck
  | _ => Term.Stuck




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
| Boolean_case : forall (x1 : eo_lit_Bool),
  (eo_is_obj (Term.Boolean x1) (Smt_Term.Boolean x1))
| Numeral_case : forall (x1 : eo_lit_Int),
  (eo_is_obj (Term.Numeral x1) (Smt_Term.Numeral x1))
| Rational_case : forall (x1 : eo_lit_Rat),
  (eo_is_obj (Term.Rational x1) (Smt_Term.Rational x1))
| String_case : forall (x1 : eo_lit_String),
  (eo_is_obj (Term.String x1) (Smt_Term.String x1))
| Binary_case : forall (x1 : eo_lit_Int)(x2 : eo_lit_Int),
  (eo_is_obj (Term.Binary x1 x2) (Smt_Term.Binary x1 x2))
| Apply_case : forall (y1 : Smt_Term)(x1 : Term)(y2 : Smt_Term)(x2 : Term),
  (eo_is_obj x1 y1) ->
  (eo_is_obj x2 y2) ->
  (eo_is_obj (Term.Apply x1 x2) (Smt_Term.Apply y1 y2))
| not_case : (eo_is_obj Term.not (Smt_Term.Id "not"))
| and_case : (eo_is_obj Term.and (Smt_Term.Id "and"))
| eq_case : (eo_is_obj Term.eq (Smt_Term.Id "="))


/-
A predicate defining when a Eunoia term corresponds to an object term that
evaluates to true or false.
(t,b) is true if t is a Eunoia term corresponding to an object term that
evaluates to b.
-/
def eo_interprets (t : Term) (b : Bool) : Prop :=
  exists (s : Object_Term), (eo_is_obj t s) /\ (obj_interprets s b)

/- The theorem statements -/

/- correctness theorem for __eo_prog_symm -/
theorem correct___eo_prog_symm (x1 : Term) :
  (eo_interprets x1 true) ->
  (Not (eo_interprets (__eo_prog_symm (Proof.pf x1)) false)) :=
by
  sorry



end Eo
