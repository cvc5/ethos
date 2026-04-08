import $EO_CALC$.SmtEval

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Eo


/- Eunoia literal evaluation defined -/

abbrev eo_lit_Bool := SmtEval.smt_lit_Bool
abbrev eo_lit_Int := SmtEval.smt_lit_Int
abbrev eo_lit_Rat := SmtEval.smt_lit_Rat
abbrev eo_lit_String := SmtEval.smt_lit_String

partial def eo_lit_ite {T : Type} (c : eo_lit_Bool) (t e : T) : T :=
  if c then t else e
abbrev eo_lit_not := SmtEval.smt_lit_not
abbrev eo_lit_and := SmtEval.smt_lit_and
abbrev eo_lit_iff := SmtEval.smt_lit_iff
abbrev eo_lit_or := SmtEval.smt_lit_or
abbrev eo_lit_xor := SmtEval.smt_lit_xor
abbrev eo_lit_zplus := SmtEval.smt_lit_zplus
abbrev eo_lit_zmult := SmtEval.smt_lit_zmult
abbrev eo_lit_zneg := SmtEval.smt_lit_zneg
abbrev eo_lit_zeq := SmtEval.smt_lit_zeq
abbrev eo_lit_zleq := SmtEval.smt_lit_zleq
abbrev eo_lit_zlt := SmtEval.smt_lit_zlt
abbrev eo_lit_div_total := SmtEval.smt_lit_div_total
abbrev eo_lit_mod_total := SmtEval.smt_lit_mod_total
abbrev eo_lit_zexp_total := SmtEval.smt_lit_zexp_total
abbrev eo_lit_int_pow2 := SmtEval.smt_lit_int_pow2
abbrev eo_lit_piand := SmtEval.smt_lit_piand
abbrev eo_lit_mk_rational := SmtEval.smt_lit_mk_rational
abbrev eo_lit_qplus := SmtEval.smt_lit_qplus
abbrev eo_lit_qmult := SmtEval.smt_lit_qmult
abbrev eo_lit_qneg := SmtEval.smt_lit_qneg
abbrev eo_lit_qeq := SmtEval.smt_lit_qeq
abbrev eo_lit_qleq := SmtEval.smt_lit_qleq
abbrev eo_lit_qlt := SmtEval.smt_lit_qlt
abbrev eo_lit_qdiv_total := SmtEval.smt_lit_qdiv_total
abbrev eo_lit_to_int := SmtEval.smt_lit_to_int
abbrev eo_lit_to_real := SmtEval.smt_lit_to_real
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
def eo_lit_str_indexof_rec (s t : eo_lit_String) (i len fuel : Nat) : eo_lit_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if String.Pos.Raw.substrEq s ⟨i⟩ t ⟨0⟩ len then
        i
      else
        eo_lit_str_indexof_rec s t (i + 1) len fuel
def eo_lit_str_indexof (s t : eo_lit_String) (i : eo_lit_Int) : eo_lit_Int :=
  if i < 0 then
    -1
  else
    let sLen := Int.toNat (eo_lit_str_len s)
    let start := Int.toNat i
    let tLen := Int.toNat (eo_lit_str_len t)
    if h : start + tLen <= sLen then
      eo_lit_str_indexof_rec s t start tLen (sLen - (start + tLen) + 1)
    else
      -1
abbrev eo_lit_str_to_code := SmtEval.smt_lit_str_to_code
abbrev eo_lit_str_from_code := SmtEval.smt_lit_str_from_code
abbrev eo_lit_streq := SmtEval.smt_lit_streq

abbrev eo_lit_bit := SmtEval.smt_lit_bit
abbrev eo_lit_msb := SmtEval.smt_lit_msb
abbrev eo_lit_binary_and := SmtEval.smt_lit_binary_and
abbrev eo_lit_binary_or := SmtEval.smt_lit_binary_or
abbrev eo_lit_binary_xor := SmtEval.smt_lit_binary_xor
abbrev eo_lit_binary_not := SmtEval.smt_lit_binary_not
abbrev eo_lit_binary_max := SmtEval.smt_lit_binary_max
abbrev eo_lit_binary_uts := SmtEval.smt_lit_binary_uts
abbrev eo_lit_binary_concat := SmtEval.smt_lit_binary_concat
abbrev eo_lit_binary_extract := SmtEval.smt_lit_binary_extract

abbrev eo_lit_Nat := SmtEval.smt_lit_Nat
abbrev eo_lit_int_to_nat := SmtEval.smt_lit_int_to_nat
abbrev eo_lit_nat_to_int := SmtEval.smt_lit_nat_to_int
abbrev eo_lit_nateq := SmtEval.smt_lit_nateq
syntax "eo_lit_nat_zero" : term
macro_rules
  | `(eo_lit_nat_zero) => `(Nat.zero)
syntax "eo_lit_nat_succ " term : term
macro_rules
  | `(eo_lit_nat_succ $x) => `(Nat.succ $x)

instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

mutual

/- Term definition -/
inductive Term : Type where
$LEAN_TERM_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/-
Eunoia datatypes.
-/
inductive Datatype : Type where
  | null : Datatype
  | sum : DatatypeCons -> Datatype -> Datatype
deriving Repr, DecidableEq, Inhabited

/-
Eunoia datatype constructors.
-/
inductive DatatypeCons : Type where
  | unit : DatatypeCons
  | cons : Term -> DatatypeCons -> DatatypeCons
deriving Repr, DecidableEq, Inhabited

end

/- Term equality -/
def eo_lit_teq : Term -> Term -> eo_lit_Bool
  | x, y => decide (x = y)

/- Term less than, based on arbitrary ordering -/
def eo_lit_tcmp (a b : Term) : eo_lit_Bool :=
  match compare a b with
  | Ordering.lt => true
  | _ => false

/- Used for defining hash -/
def eo_lit_thash : Term -> eo_lit_Int
  | _ => 0 -- FIXME

/- Proofs -/
inductive Proof : Type where
  | pf : Term -> Proof
  | Stuck : Proof

/- Definition of Eunoia signature -/

mutual

$LEAN_DEFS_TOTAL$

end

mutual

$LEAN_DEFS$

end

/- Definition of the checker -/

abbrev CIndex := eo_lit_Int

/-
-/
inductive CIndexList : Type where
  | nil : CIndexList
  | cons : CIndex -> CIndexList -> CIndexList
deriving Repr, Inhabited

/-
-/
inductive CArgList : Type where
  | nil : CArgList
  | cons : Term -> CArgList -> CArgList
deriving Repr, Inhabited

/-
-/
inductive CStateObj : Type where
  | assume : Term -> CStateObj
  | assume_push : Term -> CStateObj
  | proven : Term -> CStateObj
deriving Repr, Inhabited

/-
-/
inductive CState : Type where
  | nil : CState
  | cons : CStateObj -> CState -> CState
  | Stuck : CState
deriving Repr, Inhabited

/-
-/
inductive CRule : Type where
$LEAN_CHECKER_RULE_DEF$
deriving Repr, Inhabited

/-
-/
inductive CCmd : Type where
$LEAN_CHECKER_CMD_DEF$
deriving Repr, Inhabited

/-
-/
inductive CCmdList : Type where
  | nil : CCmdList
  | cons : CCmd -> CCmdList -> CCmdList
deriving Repr, Inhabited

$LEAN_CHECKER_DEFS$

/-- API for logos -/
def logos_init_state : CState := CState.nil
def logos_invoke_assume (s : CState) (A : Term) : CState := (CState.cons (CStateObj.assume A) s)
def logos_invoke_cmd (s : CState) (c :CCmd) : CState := (__eo_invoke_cmd s c)
def logos_state_is_refutation (s : CState) : eo_lit_Bool := (__eo_state_is_refutation s)

end Eo
