set_option linter.unusedVariables false

namespace Eo

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

/------------------------ should move ------------------------/

/- 
SMT-LIB types.
-/
inductive SmtType : Type where
  | Stuck : Term
  | Bool : Term

deriving DecidableEq

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
  | Stuck : Term
  | Boolean : eo_lit_Bool -> Term
  | Numeral : eo_lit_Int -> Term
  | Rational : eo_lit_Rat -> Term
  | String : eo_lit_String -> Term
  | Binary : eo_lit_Int -> eo_lit_Int -> Term
  | Apply : SmtTerm -> SmtTerm -> Term
  | Var : eo_lit_String -> SmtType -> Term
  | not : Term
  | and : Term
  | eq : Term

deriving DecidableEq

/- 
SMT-LIB values.
-/
inductive SmtValue : Type where
  | Boolean : eo_lit_Bool -> Term
  | Numeral : eo_lit_Int -> Term
  | Rational : eo_lit_Rat -> Term
  | String : eo_lit_String -> Term
  | Binary : eo_lit_Int -> eo_lit_Int -> Term
  | Map : Term -> Term
  | Apply : SmtValue -> SmtValue -> Term
  | NotValue : Term

deriving DecidableEq



/-
A definition of terms in the object language.
This is to be defined externally.
-/
abbrev Object_Term := SmtTerm

/-
A predicate defining a relation on terms in the object language and Booleans
such that (s,b) is true if s evaluates to b.
This is to be defined externally.
-/
axiom obj_interprets : Object_Term -> Bool -> Prop

/------------------------------------------------/
  
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


def __eo_ite : Term -> Term -> Term -> Term
  | x1, x2, x3 => (eo_lit_ite (eo_lit_teq x1 (Term.Boolean true)) x2 (eo_lit_ite (eo_lit_teq x1 (Term.Boolean false)) x3 Term.Stuck))


def __eo_requires : Term -> Term -> Term -> Term
  | x1, x2, x3 => (eo_lit_ite (eo_lit_teq x1 x2) (eo_lit_ite (eo_lit_not (eo_lit_teq x1 Term.Stuck)) x3 Term.Stuck) Term.Stuck)


def __eo_mk_apply : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, x2 => (Term.Apply x1 x2)


def __eo_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Boolean (eo_lit_teq s t))


def __mk_symm : Term -> Term
  | Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.eq t1) t2) => (Term.Apply (Term.Apply Term.eq t2) t1)
  | (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) t2)) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t2) t1))
  | _ => Term.Stuck


def __eo_prog_symm : Proof -> Term
  | (Proof.pf F) => (__mk_symm F)
  | _ => Term.Stuck


def __eo_l_1___smtx_msm_lookup : Term -> SmtValue -> SmtValue
  | (Term.cons j e m), i => (__smtx_msm_lookup m i)
  | (Term.default e), i => e


def __smtx_msm_lookup : Term -> SmtValue -> SmtValue
  | (Term.cons i e m), __eo_lv_i_2 => (__eo_ite (__eo_eq i __eo_lv_i_2) e (__eo_l_1___smtx_msm_lookup (Term.cons i e m) __eo_lv_i_2))
  | __eo_dv_1, __eo_dv_2 => (__eo_l_1___smtx_msm_lookup __eo_dv_1 __eo_dv_2)


def __smtx_model_eval_apply : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Apply f v), i => (SmtValue.Apply (SmtValue.Apply f v) i)
  | (SmtValue.Map m), i => (__smtx_msm_lookup m i)
  | v, i => SmtValue.NotValue


def __smtx_model_eval_eq : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean b1), (SmtValue.Boolean b2) => (SmtValue.Boolean (eo_lit_iff b1 b2))
  | (SmtValue.Boolean b1), t2 => SmtValue.NotValue
  | t1, (SmtValue.Boolean b2) => SmtValue.NotValue
  | (SmtValue.Numeral n1), (SmtValue.Numeral n2) => (SmtValue.Boolean (eo_lit_zeq n1 n2))
  | (SmtValue.Numeral n1), t2 => SmtValue.NotValue
  | t1, (SmtValue.Numeral n2) => SmtValue.NotValue
  | (SmtValue.Rational r1), (SmtValue.Rational r2) => (SmtValue.Boolean (eo_lit_qeq r1 r2))
  | (SmtValue.Rational r1), t2 => SmtValue.NotValue
  | t1, (SmtValue.Rational r2) => SmtValue.NotValue
  | (SmtValue.String s1), (SmtValue.String s2) => (SmtValue.Boolean (eo_lit_veq (SmtValue.String s1) (SmtValue.String s2)))
  | (SmtValue.String s1), t2 => SmtValue.NotValue
  | t1, (SmtValue.String s2) => SmtValue.NotValue
  | (SmtValue.Binary w1 n1), (SmtValue.Binary w2 n2) => (eo_lit_ite (eo_lit_zeq w1 w2) (SmtValue.Boolean (eo_lit_veq (SmtValue.Binary w1 n1) (SmtValue.Binary w2 n2))) SmtValue.NotValue)
  | (SmtValue.Binary w1 n1), t2 => SmtValue.NotValue
  | t1, (SmtValue.Binary w2 n2) => SmtValue.NotValue
  | SmtValue.NotValue, t2 => SmtValue.NotValue
  | t1, SmtValue.NotValue => SmtValue.NotValue
  | t1, t2 => (SmtValue.Boolean (eo_lit_veq t1 t2))


def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (eo_lit_not x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (eo_lit_and x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval : SmtTerm -> SmtValue
  | (SmtTerm.Apply SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x1) x2) => (__smtx_model_eval_and (__smtx_model_eval x1) (__smtx_model_eval x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) => (__smtx_model_eval_eq (__smtx_model_eval x1) (__smtx_model_eval x2))
  | (SmtTerm.Apply f y) => (__smtx_model_eval_apply (__smtx_model_eval f) (__smtx_model_eval y))


def __eo_to_smt_type : Term -> SmtType
  | Term.Bool => SmtType.Bool
  | T => SmtType.Stuck


def __eo_to_smt : Term -> SmtTerm
  | (Term.Boolean b) => (SmtTerm.Boolean b)
  | (Term.Numeral n) => (SmtTerm.Numeral n)
  | (Term.Rational r) => (SmtTerm.Rational r)
  | (Term.String s) => (SmtTerm.String s)
  | (Term.Binary w n) => (SmtTerm.Binary w n)
  | (Term.Var s T) => (SmtTerm.Var s (__eo_to_smt_type T))
  | Term.not => SmtTerm.not
  | Term.and => SmtTerm.and
  | Term.eq => SmtTerm.eq
  | (Term.Apply f y) => (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y))
  | y => SmtTerm.Stuck




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
| intro (x : Term) : eo_is_obj x (__eo_to_obj x)


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
