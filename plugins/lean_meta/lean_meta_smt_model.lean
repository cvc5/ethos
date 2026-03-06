import Cpc.SmtEval

set_option linter.unusedVariables false

namespace Smtm

/- SMT literal evaluation defined -/

abbrev smt_lit_Bool := SmtEval.smt_lit_Bool
abbrev smt_lit_Int := SmtEval.smt_lit_Int
abbrev smt_lit_Rat := SmtEval.smt_lit_Rat
abbrev smt_lit_String := SmtEval.smt_lit_String
abbrev smt_lit_RegLan := String --FIXME

def smt_lit_ite {T : Type} (c : smt_lit_Bool) (t e : T) : T :=
  if c then t else e
abbrev smt_lit_not := SmtEval.smt_lit_not
abbrev smt_lit_and := SmtEval.smt_lit_and
abbrev smt_lit_iff := SmtEval.smt_lit_iff
abbrev smt_lit_or := SmtEval.smt_lit_or
abbrev smt_lit_xor := SmtEval.smt_lit_xor
abbrev smt_lit_zplus := SmtEval.smt_lit_zplus
abbrev smt_lit_zmult := SmtEval.smt_lit_zmult
abbrev smt_lit_zneg := SmtEval.smt_lit_zneg
abbrev smt_lit_zeq := SmtEval.smt_lit_zeq
abbrev smt_lit_zleq := SmtEval.smt_lit_zleq
abbrev smt_lit_zlt := SmtEval.smt_lit_zlt
abbrev smt_lit_div := SmtEval.smt_lit_div
abbrev smt_lit_mod := SmtEval.smt_lit_mod
abbrev smt_lit_int_pow2 := SmtEval.smt_lit_int_pow2
abbrev smt_lit_piand := SmtEval.smt_lit_piand
abbrev smt_lit_mk_rational := SmtEval.smt_lit_mk_rational
abbrev smt_lit_qplus := SmtEval.smt_lit_qplus
abbrev smt_lit_qmult := SmtEval.smt_lit_qmult
abbrev smt_lit_qneg := SmtEval.smt_lit_qneg
abbrev smt_lit_qeq := SmtEval.smt_lit_qeq
abbrev smt_lit_qleq := SmtEval.smt_lit_qleq
abbrev smt_lit_qlt := SmtEval.smt_lit_qlt
abbrev smt_lit_qdiv := SmtEval.smt_lit_qdiv
abbrev smt_lit_to_int := SmtEval.smt_lit_to_int
abbrev smt_lit_to_real := SmtEval.smt_lit_to_real
abbrev smt_lit_str_len := SmtEval.smt_lit_str_len
abbrev smt_lit_str_concat := SmtEval.smt_lit_str_concat
abbrev smt_lit_str_substr := SmtEval.smt_lit_str_substr
abbrev smt_lit_str_indexof := SmtEval.smt_lit_str_indexof
abbrev smt_lit_str_to_code := SmtEval.smt_lit_str_to_code
abbrev smt_lit_str_from_code := SmtEval.smt_lit_str_from_code

abbrev smt_lit_bit := SmtEval.smt_lit_bit
abbrev smt_lit_msb := SmtEval.smt_lit_msb
abbrev smt_lit_binary_and := SmtEval.smt_lit_binary_and
abbrev smt_lit_binary_or := SmtEval.smt_lit_binary_or
abbrev smt_lit_binary_xor := SmtEval.smt_lit_binary_xor
abbrev smt_lit_binary_not := SmtEval.smt_lit_binary_not
abbrev smt_lit_binary_max := SmtEval.smt_lit_binary_max
abbrev smt_lit_binary_uts := SmtEval.smt_lit_binary_uts
abbrev smt_lit_binary_concat := SmtEval.smt_lit_binary_concat
abbrev smt_lit_binary_extract := SmtEval.smt_lit_binary_extract

-- SMT Beyond Eunoia

def smt_lit_streq : smt_lit_String -> smt_lit_String -> smt_lit_Bool
  | x, y => decide (x = y)

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
def smt_lit_re_diff : smt_lit_RegLan -> smt_lit_RegLan -> smt_lit_RegLan
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
def smt_lit_re_allchar : smt_lit_RegLan := "" --FIXME
def smt_lit_re_none : smt_lit_RegLan := "" --FIXME
def smt_lit_re_all : smt_lit_RegLan := "" --FIXME

-- Partial semantics

def smt_lit_qdiv_by_zero : smt_lit_Rat -> smt_lit_Rat
  | x => x -- FIXME
def smt_lit_div_by_zero : smt_lit_Int -> smt_lit_Int
  | x => x -- FIXME
def smt_lit_mod_by_zero : smt_lit_Int -> smt_lit_Int
  | x => x -- FIXME


mutual

/- 
SMT-LIB types.
-/
inductive SmtType : Type where
$LEAN_SMT_TYPE_DEF$
deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB terms.
-/
inductive SmtTerm : Type where
$LEAN_SMT_TERM_DEF$
deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB values.
-/
inductive SmtValue : Type where
$LEAN_SMT_VALUE_DEF$
deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB map values.
-/
inductive SmtMap : Type where
  | cons : SmtValue -> SmtValue -> SmtMap -> SmtMap
  | default : SmtType -> SmtValue -> SmtMap
deriving Repr, DecidableEq, Inhabited

/- 
SMT-LIB sequence values.
-/
inductive SmtSeq : Type where
  | cons : SmtValue -> SmtSeq -> SmtSeq
  | empty : SmtType -> SmtSeq
deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB datatypes.
-/
inductive SmtDatatype : Type where
  | null : SmtDatatype
  | sum : SmtDatatypeCons -> SmtDatatype -> SmtDatatype
deriving Repr, DecidableEq, Inhabited

/-
SMT-LIB datatype constructors.
-/
inductive SmtDatatypeCons : Type where
  | unit : SmtDatatypeCons
  | cons : SmtType -> SmtDatatypeCons -> SmtDatatypeCons
deriving Repr, DecidableEq, Inhabited

end

/-
SMT-LIB model
-/
abbrev SmtModel := Int -- FIXME

def __smtx_model_lookup : SmtModel -> smt_lit_Int -> SmtType -> SmtValue
  | _, _, _ => (SmtValue.Boolean true) -- FIXME


/- Type equality -/
def smt_lit_Teq : SmtType -> SmtType -> smt_lit_Bool
  | x, y => decide (x = y)
/- Value equality -/
def smt_lit_veq : SmtValue -> SmtValue -> smt_lit_Bool
  | x, y => decide (x = y)
/- Used for ordering values -/
def __smtx_value_hash : SmtValue -> smt_lit_Int
  | _ => 0 -- FIXME
  
/- exists -/
def smt_lit_tforall : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _ => (SmtValue.Boolean true) -- FIXME
/- forall -/
def smt_lit_texists : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _ => (SmtValue.Boolean true) -- FIXME
/- choice -/
def smt_lit_tchoice : SmtModel -> smt_lit_String -> SmtType -> SmtTerm -> SmtValue
  | _, _, _ => (SmtValue.Boolean true) -- FIXME

/- Definition of SMT-LIB model semantics -/

mutual

$LEAN_SMT_EVAL_DEFS$

end

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_interprets : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      exists M : SmtModel, (__smtx_model_eval M t) = (SmtValue.Boolean true) ->
      smt_interprets t true
  | intro_false (t : SmtTerm) :
      forall M : SmtModel, (__smtx_model_eval M t) = (SmtValue.Boolean false)->
      smt_interprets t false

/- FIXME inductive smt_model_well_typed : SmtModel -> Prop, based on smt axiom -/

/- ---------------------------------------------- -/

end Smtm
