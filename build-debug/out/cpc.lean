set_option linter.unusedVariables false

namespace Eo

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

-- SMT Beyond Eunoia

def smt_lit_int_pow2 : smt_lit_Int -> smt_lit_Int
  | _ => 0 -- FIXME
def smt_lit_int_log2 : smt_lit_Int -> smt_lit_Int
  | _ => 0 -- FIXME

def smt_lit_str_lt : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_from_int : smt_lit_Int -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_to_int : smt_lit_String -> smt_lit_Int
  | _ => 0 -- FIXME
def smt_lit_str_to_upper : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_to_lower : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_update : smt_lit_String -> smt_lit_Int -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_rev : smt_lit_String -> smt_lit_String
  | _ => "" -- FIXME
def smt_lit_str_replace : smt_lit_String -> smt_lit_String -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_replace_all : smt_lit_String -> smt_lit_String -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_contains : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_to_re : smt_lit_String -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_mult : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_plus : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_comp : smt_lit_RegLan -> smt_lit_RegLan
  | _ => "" -- FIXME
def smt_lit_re_concat : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_inter : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_union : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_re_range : smt_lit_String -> smt_lit_String -> smt_lit_RegLan
  | _, _ => "" -- FIXME
def smt_lit_str_in_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Bool
  | _, _ => false -- FIXME
def smt_lit_str_indexof_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_Int -> smt_lit_Int
  | _, _, _ => 0 -- FIXME
def smt_lit_str_replace_re : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME
def smt_lit_str_replace_re_all : smt_lit_String -> smt_lit_RegLan -> smt_lit_String -> smt_lit_String
  | _, _, _ => "" -- FIXME

/- ----------------------- should move ----------------------- -/

mutual

/- 
SMT-LIB types.
-/
inductive SmtType : Type where
  | None : SmtType
  | Bool : SmtType
  | Int : SmtType
  | Real : SmtType
  | String : SmtType
  | RegLan : SmtType
  | BitVec : smt_lit_Int -> SmtType
  | Map : SmtType -> SmtType -> SmtType
  | DtCons : SmtType -> SmtType -> SmtType
  | Seq : SmtType -> SmtType
  | Datatype : smt_lit_String -> SmtDatatype -> SmtType
  | Char : SmtType

deriving DecidableEq

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
  | None : SmtTerm
  | Boolean : smt_lit_Bool -> SmtTerm
  | Numeral : smt_lit_Int -> SmtTerm
  | Rational : smt_lit_Rat -> SmtTerm
  | String : smt_lit_String -> SmtTerm
  | Binary : smt_lit_Int -> smt_lit_Int -> SmtTerm
  | Apply : SmtTerm -> SmtTerm -> SmtTerm
  | Var : smt_lit_String -> SmtType -> SmtTerm
  | exists : smt_lit_String -> SmtType -> SmtTerm
  | forall : smt_lit_String -> SmtType -> SmtTerm
  | lambda : smt_lit_String -> SmtType -> SmtTerm
  | DtCons : SmtType -> smt_lit_Int -> SmtTerm
  | DtSel : SmtType -> smt_lit_Int -> smt_lit_Int -> SmtTerm
  | DtTester : SmtType -> smt_lit_Int -> SmtTerm
  | DtUpdater : SmtType -> smt_lit_Int -> smt_lit_Int -> SmtTerm
  | Const : SmtValue -> SmtTerm
  | not : SmtTerm
  | and : SmtTerm
  | eq : SmtTerm

deriving DecidableEq

/- 
SMT-LIB values.
-/
inductive SmtValue : Type where
  | NotValue : SmtValue
  | Boolean : smt_lit_Bool -> SmtValue
  | Numeral : smt_lit_Int -> SmtValue
  | Rational : smt_lit_Rat -> SmtValue
  | String : smt_lit_String -> SmtValue
  | Binary : smt_lit_Int -> smt_lit_Int -> SmtValue
  | Map : SmtMap -> SmtValue
  | Seq : SmtSeq -> SmtValue
  | RegLan : smt_lit_RegLan -> SmtValue
  | Lambda : smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | DtCons : SmtType -> smt_lit_Int -> SmtValue
  | Apply : SmtValue -> SmtValue -> SmtValue

deriving DecidableEq

/-
SMT-LIB map values.
-/
inductive SmtMap : Type where
  | cons : SmtValue -> SmtValue -> SmtMap -> SmtMap
  | default : SmtType -> SmtValue -> SmtMap
deriving DecidableEq

/- 
SMT-LIB sequence values.
-/
inductive SmtSeq : Type where
  | cons : SmtValue -> SmtSeq -> SmtSeq
  | empty : SmtType -> SmtSeq
deriving DecidableEq

/-
SMT-LIB datatypes.
-/
inductive SmtDatatype : Type where
  | null : SmtDatatype
  | sum : SmtDatatypeCons -> SmtDatatype -> SmtDatatype
deriving DecidableEq

/-
SMT-LIB datatype constructors.
-/
inductive SmtDatatypeCons : Type where
  | unit : SmtDatatypeCons
  | cons : SmtType -> SmtDatatypeCons -> SmtDatatypeCons
deriving DecidableEq

end

/- Type equality -/
def smt_lit_Teq : SmtType -> SmtType -> smt_lit_Bool
  | x, y => decide (x = y)
/- Value equality -/
def smt_lit_veq : SmtValue -> SmtValue -> smt_lit_Bool
  | x, y => decide (x = y)

/- exists -/
def smt_lit___smtx_model_eval_exists : smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _ => (SmtValue.Boolean true) -- FIXME
/- forall -/
def smt_lit___smtx_model_eval_forall : smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _ => (SmtValue.Boolean true) -- FIXME

/- Definition of SMT-LIB model semantics -/

mutual

def __smtx_pow2 : smt_lit_Int -> smt_lit_Int
  | i => (smt_lit_ite (smt_lit_zleq i 0) 1 (smt_lit_zmult 2 (__smtx_pow2 (smt_lit_zplus i (smt_lit_zneg 1)))))


def __vsm_apply_head : SmtValue -> SmtValue
  | (SmtValue.Apply f a) => (__vsm_apply_head f)
  | a => a


def __vsm_apply_arg_nth : SmtValue -> smt_lit_Int -> SmtValue
  | (SmtValue.Apply f a), n => (smt_lit_ite (smt_lit_zeq n 0) a (__vsm_apply_arg_nth f (smt_lit_zplus n (smt_lit_zneg 1))))
  | a, n => SmtValue.NotValue


def __smtx_msm_lookup : SmtMap -> SmtValue -> SmtValue
  | (SmtMap.cons j e m), i => (smt_lit_ite (smt_lit_veq j i) e (__smtx_msm_lookup m i))
  | (SmtMap.default T e), i => e


def __smtx_typeof_map_value : SmtMap -> SmtType
  | (SmtMap.cons i e m) => (smt_lit_ite (smt_lit_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e)) (__smtx_typeof_map_value m)) (__smtx_typeof_map_value m) SmtType.None)
  | (SmtMap.default T e) => (SmtType.Map T (__smtx_typeof_value e))


def __smtx_typeof_seq_value : SmtSeq -> SmtType
  | (SmtSeq.cons v vs) => (smt_lit_ite (smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)) (__smtx_typeof_seq_value vs) SmtType.None)
  | (SmtSeq.empty T) => (SmtType.Seq T)


def __smtx_typeof_dt_cons_value_rec2 : SmtType -> SmtDatatypeCons -> SmtType
  | T, (SmtDatatypeCons.cons U c) => (SmtType.DtCons U (__smtx_typeof_dt_cons_value_rec2 T c))
  | T, SmtDatatypeCons.unit => T


def __smtx_typeof_dt_cons_value_rec : SmtType -> SmtDatatype -> smt_lit_Int -> SmtType
  | T, (SmtDatatype.sum c d), 0 => (__smtx_typeof_dt_cons_value_rec2 T c)
  | T, (SmtDatatype.sum c d), n => (__smtx_typeof_dt_cons_value_rec T d (smt_lit_zplus n (smt_lit_zneg 1)))
  | T, d, n => SmtType.None


def __smtx_typeof_dt_cons_value : SmtType -> smt_lit_Int -> SmtType
  | (SmtType.Datatype s d), n => (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) d n)
  | T, n => SmtType.None


def __smtx_typeof_apply_value : SmtType -> SmtType -> SmtType
  | (SmtType.DtCons T U), V => (smt_lit_ite (smt_lit_Teq T V) U SmtType.None)
  | T, U => SmtType.None


def __smtx_typeof_value : SmtValue -> SmtType
  | (SmtValue.Boolean b) => SmtType.Bool
  | (SmtValue.Numeral n) => SmtType.Int
  | (SmtValue.Rational q) => SmtType.Real
  | (SmtValue.String s) => SmtType.String
  | (SmtValue.Binary w n) => (smt_lit_ite (smt_lit_zleq 0 w) (SmtType.BitVec w) SmtType.None)
  | (SmtValue.RegLan r) => SmtType.RegLan
  | (SmtValue.Map m) => (__smtx_typeof_map_value m)
  | (SmtValue.Seq ss) => (__smtx_typeof_seq_value ss)
  | (SmtValue.DtCons T n) => (__smtx_typeof_dt_cons_value T n)
  | (SmtValue.Apply f v) => (__smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v))
  | v => SmtType.None


def __smtx_model_eval_eq : SmtValue -> SmtValue -> SmtValue
  | t1, t2 => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) (__smtx_typeof_value t2)) (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value t1) SmtType.None) SmtValue.NotValue (SmtValue.Boolean (smt_lit_veq t1 t2))) SmtValue.NotValue)


def __smtx_is_var : smt_lit_String -> SmtType -> SmtTerm -> smt_lit_Bool
  | s1, T1, (SmtTerm.Var s2 T2) => (smt_lit_and (smt_lit_streq s1 s2) (smt_lit_Teq T1 T2))
  | s1, T1, x => false


def __smtx_is_binder_x : smt_lit_String -> SmtType -> SmtTerm -> smt_lit_Bool
  | s1, T1, (SmtTerm.exists s2 T2) => (__smtx_is_var s1 T1 (SmtTerm.Var s2 T2))
  | s1, T1, (SmtTerm.forall s2 T2) => (__smtx_is_var s1 T1 (SmtTerm.Var s2 T2))
  | s1, T1, (SmtTerm.lambda s2 T2) => (__smtx_is_var s1 T1 (SmtTerm.Var s2 T2))
  | s1, T1, x => false


def __smtx_substitute : smt_lit_String -> SmtType -> SmtValue -> SmtTerm -> SmtTerm
  | s, T, v, (SmtTerm.Apply f a) => (smt_lit_ite (__smtx_is_binder_x s T f) (SmtTerm.Apply f a) (SmtTerm.Apply (__smtx_substitute s T v f) (__smtx_substitute s T v a)))
  | s, T, v, z => (smt_lit_ite (__smtx_is_var s T z) (SmtTerm.Const v) z)


def __smtx_model_eval_dt_cons : SmtType -> smt_lit_Int -> SmtValue
  | T, n => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_dt_cons_value T n) SmtType.None) SmtValue.NotValue (SmtValue.DtCons T n))


def __smtx_model_eval_dt_sel : SmtType -> smt_lit_Int -> smt_lit_Int -> SmtValue -> SmtValue
  | T, n, m, v1 => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v1) T) (smt_lit_ite (smt_lit_veq (__vsm_apply_head v1) (SmtValue.DtCons T n)) (__vsm_apply_arg_nth v1 n) SmtValue.NotValue) SmtValue.NotValue)


def __smtx_model_eval_dt_tester : SmtType -> smt_lit_Int -> SmtValue -> SmtValue
  | T, n, v1 => (smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v1) T) (SmtValue.Boolean (smt_lit_veq (__vsm_apply_head v1) (SmtValue.DtCons T n))) SmtValue.NotValue)


def __smtx_model_eval_dt_updater : SmtType -> smt_lit_Int -> smt_lit_Int -> SmtValue -> SmtValue -> SmtValue
  | T, n, m, v1, v2 => SmtValue.NotValue


def __smtx_model_eval_apply : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Apply f v), i => (SmtValue.Apply (SmtValue.Apply f v) i)
  | (SmtValue.Map m), i => (__smtx_msm_lookup m i)
  | (SmtValue.Lambda s T t), i => (__smtx_model_eval (__smtx_substitute s T i t))
  | v, i => SmtValue.NotValue


def __smtx_model_eval_not : SmtValue -> SmtValue
  | (SmtValue.Boolean x1) => (SmtValue.Boolean (smt_lit_not x1))
  | t1 => SmtValue.NotValue


def __smtx_model_eval_and : SmtValue -> SmtValue -> SmtValue
  | (SmtValue.Boolean x1), (SmtValue.Boolean x2) => (SmtValue.Boolean (smt_lit_and x1 x2))
  | t1, t2 => SmtValue.NotValue


def __smtx_model_eval : SmtTerm -> SmtValue
  | (SmtTerm.Boolean b) => (SmtValue.Boolean b)
  | (SmtTerm.Numeral n) => (SmtValue.Numeral n)
  | (SmtTerm.Rational r) => (SmtValue.Rational r)
  | (SmtTerm.String s) => (SmtValue.String s)
  | (SmtTerm.Binary w n) => (smt_lit_ite (smt_lit_and (smt_lit_zleq 0 w) (smt_lit_zeq n (smt_lit_mod n (__smtx_pow2 w)))) (SmtValue.Binary w n) SmtValue.NotValue)
  | (SmtTerm.Apply SmtTerm.not x1) => (__smtx_model_eval_not (__smtx_model_eval x1))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x1) x2) => (__smtx_model_eval_and (__smtx_model_eval x1) (__smtx_model_eval x2))
  | (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) => (__smtx_model_eval_eq (__smtx_model_eval x1) (__smtx_model_eval x2))
  | (SmtTerm.Apply (SmtTerm.exists s T) x1) => (smt_lit___smtx_model_eval_exists s T x1)
  | (SmtTerm.Apply (SmtTerm.forall s T) x1) => (smt_lit___smtx_model_eval_forall s T x1)
  | (SmtTerm.Apply (SmtTerm.lambda s T) x1) => (SmtValue.Lambda s T x1)
  | (SmtTerm.DtCons T n) => (__smtx_model_eval_dt_cons T n)
  | (SmtTerm.Apply (SmtTerm.DtSel T n m) x1) => (__smtx_model_eval_dt_sel T n m (__smtx_model_eval x1))
  | (SmtTerm.Apply (SmtTerm.DtTester T n) x1) => (__smtx_model_eval_dt_tester T n (__smtx_model_eval x1))
  | (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.DtUpdater T n m) x1) x2) => (__smtx_model_eval_dt_updater T n m (__smtx_model_eval x1) (__smtx_model_eval x2))
  | (SmtTerm.Apply f x1) => (__smtx_model_eval_apply (__smtx_model_eval f) (__smtx_model_eval x1))
  | (SmtTerm.Const v) => v
  | x1 => SmtValue.NotValue




end

inductive smt_interprets : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (__smtx_model_eval t) = (SmtValue.Boolean true) ->
      smt_interprets t true
  | intro_false (t : SmtTerm) :
      (__smtx_model_eval t) = (SmtValue.Boolean false)->
      smt_interprets t false

/- ---------------------------------------------- -/
  

/- Eunoia literal evaluation defined -/

abbrev eo_lit_Bool := smt_lit_Bool
abbrev eo_lit_Int := smt_lit_Int
abbrev eo_lit_Rat := smt_lit_Rat
abbrev eo_lit_String := smt_lit_String

def eo_lit_ite {T : Type} (c : eo_lit_Bool) (t e : T) : T :=
  if c then t else e
abbrev eo_lit_not  := smt_lit_not
abbrev eo_lit_and  := smt_lit_and
abbrev eo_lit_iff  := smt_lit_iff
abbrev eo_lit_or  := smt_lit_or
abbrev eo_lit_xor  := smt_lit_xor
abbrev eo_lit_zplus  := smt_lit_zplus
abbrev eo_lit_zmult  := smt_lit_zmult
abbrev eo_lit_zneg  := smt_lit_zneg
abbrev eo_lit_zeq  := smt_lit_zeq
abbrev eo_lit_zleq  := smt_lit_zleq
abbrev eo_lit_zlt  := smt_lit_zlt
abbrev eo_lit_div  := smt_lit_div
abbrev eo_lit_mod  := smt_lit_mod
abbrev eo_lit_mk_rational  := smt_lit_mk_rational
abbrev eo_lit_qplus  := smt_lit_qplus
abbrev eo_lit_qmult  := smt_lit_qmult
abbrev eo_lit_qneg  := smt_lit_qneg
abbrev eo_lit_qeq  := smt_lit_qeq
abbrev eo_lit_qleq  := smt_lit_qleq
abbrev eo_lit_qlt  := smt_lit_qlt
abbrev eo_lit_qdiv  := smt_lit_qdiv
abbrev eo_lit_to_int  := smt_lit_to_int
abbrev eo_lit_to_real  := smt_lit_to_real
abbrev eo_lit_str_len  := smt_lit_str_len
abbrev eo_lit_str_concat  := smt_lit_str_concat
abbrev eo_lit_str_substr := smt_lit_str_substr
abbrev eo_lit_str_indexof_rec := smt_lit_str_indexof_rec
abbrev eo_lit_str_indexof := smt_lit_str_indexof
abbrev eo_lit_str_to_code := smt_lit_str_to_code
abbrev eo_lit_str_from_code := smt_lit_str_from_code

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

/- Definition of Eunoia signature -/

mutual

def __eo_proven : Proof -> Term
  | (Proof.pf F) => F
  | _ => Term.Stuck


def __eo_Bool : Term := Term.Bool
def __eo_bool : smt_lit_Bool -> Term
  | x => (Term.Boolean x)


def __eo_numeral : smt_lit_Int -> Term
  | x => (Term.Numeral x)


def __eo_rational : smt_lit_Rat -> Term
  | x => (Term.Rational x)


def __eo_string : smt_lit_String -> Term
  | x => (Term.String x)


def __eo_binary : smt_lit_Int -> smt_lit_Int -> Term
  | w, v => (Term.Binary w v)


def __eo_Type : Term := Term.Type
def __eo_stuck : Term := Term.Stuck
def __eo_apply : Term -> Term -> Term
  | x, y => (Term.Apply x y)


def __eo_fun_type : Term := Term.FunType
def __eo_Var : smt_lit_String -> Term -> Term
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


def __eo_to_smt_type : Term -> SmtType
  | Term.Bool => SmtType.Bool
  | Term.Int => SmtType.Int
  | Term.Real => SmtType.Real
  | (Term.Apply Term.BitVec (Term.Numeral n1)) => (SmtType.BitVec n1)
  | Term.Char => SmtType.Char
  | (Term.Apply Term.Seq x1) => (SmtType.Seq (__eo_to_smt_type x1))
  | T => SmtType.None


def __eo_to_smt : Term -> SmtTerm
  | (Term.Boolean b) => (SmtTerm.Boolean b)
  | (Term.Numeral n) => (SmtTerm.Numeral n)
  | (Term.Rational r) => (SmtTerm.Rational r)
  | (Term.String s) => (SmtTerm.String s)
  | (Term.Binary w n) => (SmtTerm.Binary w n)
  | (Term.Var s T) => (SmtTerm.Var s (__eo_to_smt_type T))
  | (Term.Apply Term.not x1) => (SmtTerm.Apply SmtTerm.not (__eo_to_smt x1))
  | (Term.Apply (Term.Apply Term.and x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply (Term.Apply Term.eq x1) x2) => (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x1)) (__eo_to_smt x2))
  | (Term.Apply f y) => (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y))
  | y => SmtTerm.None




end

/- Definitions for theorems -/

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
abbrev obj_interprets := smt_interprets

/-
An inductive predicate defining the correspondence between Eunoia terms
and terms in the object language.
(t,s) is true if the Eunoia term represents a term s in the object language.
This is to be custom defined in the Eunoia-to-Lean compiler based on the
target definition of Object_Term.
-/
inductive eo_is_obj : Term -> Object_Term -> Prop
  | intro (x : Term) : eo_is_obj x (__eo_to_smt x)


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



/- ---------------------------------------------- -/


/- ---------------------------------------------- -/

end Eo
