import Cpc.SmtEval

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
abbrev eo_lit_div := SmtEval.smt_lit_div
abbrev eo_lit_mod := SmtEval.smt_lit_mod
abbrev eo_lit_int_pow2 := SmtEval.smt_lit_int_pow2
abbrev eo_lit_piand := SmtEval.smt_lit_piand
abbrev eo_lit_mk_rational := SmtEval.smt_lit_mk_rational
abbrev eo_lit_qplus := SmtEval.smt_lit_qplus
abbrev eo_lit_qmult := SmtEval.smt_lit_qmult
abbrev eo_lit_qneg := SmtEval.smt_lit_qneg
abbrev eo_lit_qeq := SmtEval.smt_lit_qeq
abbrev eo_lit_qleq := SmtEval.smt_lit_qleq
abbrev eo_lit_qlt := SmtEval.smt_lit_qlt
abbrev eo_lit_qdiv := SmtEval.smt_lit_qdiv
abbrev eo_lit_to_int := SmtEval.smt_lit_to_int
abbrev eo_lit_to_real := SmtEval.smt_lit_to_real
abbrev eo_lit_str_len := SmtEval.smt_lit_str_len
abbrev eo_lit_str_concat := SmtEval.smt_lit_str_concat
abbrev eo_lit_str_substr := SmtEval.smt_lit_str_substr
abbrev eo_lit_str_indexof := SmtEval.smt_lit_str_indexof
abbrev eo_lit_str_to_code := SmtEval.smt_lit_str_to_code
abbrev eo_lit_str_from_code := SmtEval.smt_lit_str_from_code

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

instance : Ord Rat where
  compare a b :=
    -- compare a.num / a.den vs b.num / b.den by cross-multiplication
    compare (a.num * Int.ofNat b.den) (b.num * Int.ofNat a.den)

mutual

/- Term definition -/
inductive Term : Type where
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
  | DatatypeType : eo_lit_String -> Datatype -> Term
  | DtCons : eo_lit_String -> Datatype -> eo_lit_Int -> Term
  | DtSel : eo_lit_String -> Datatype -> eo_lit_Int -> eo_lit_Int -> Term
  | USort : eo_lit_Int -> Term
  | UConst : eo_lit_Int -> Term -> Term
  | not : Term
  | and : Term
  | eq : Term

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

partial def __eo_mk_apply : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, x2 => (Term.Apply x1 x2)


partial def __eo_binary_mod_w (w : eo_lit_Int) (n : eo_lit_Int) : Term :=
  (Term.Binary w (eo_lit_mod n (eo_lit_int_pow2 w)))

partial def __eo_is_ok : Term -> Term
  | x => (Term.Boolean (eo_lit_not (eo_lit_teq x Term.Stuck)))


partial def __eo_ite : Term -> Term -> Term -> Term
  | x1, x2, x3 => (eo_lit_ite (eo_lit_teq x1 (Term.Boolean true)) x2 (eo_lit_ite (eo_lit_teq x1 (Term.Boolean false)) x3 Term.Stuck))


partial def __eo_requires : Term -> Term -> Term -> Term
  | x1, x2, x3 => (eo_lit_ite (eo_lit_teq x1 x2) (eo_lit_ite (eo_lit_not (eo_lit_teq x1 Term.Stuck)) x3 Term.Stuck) Term.Stuck)


partial def __eo_and : Term -> Term -> Term
  | (Term.Boolean b1), (Term.Boolean b2) => (Term.Boolean (eo_lit_and b1 b2))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => (eo_lit_ite (eo_lit_teq (Term.Numeral w1) (Term.Numeral w2)) (eo_lit_ite (eo_lit_not (eo_lit_teq (Term.Numeral w1) Term.Stuck)) (Term.Binary w1 (eo_lit_mod (eo_lit_binary_and w1 n1 n2) (eo_lit_int_pow2 w1))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


partial def __eo_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Boolean (eo_lit_teq s t))


partial def __eo_prog_contra : Proof -> Proof -> Term
  | (Proof.pf F), (Proof.pf (Term.Apply Term.not __eo_lv_F_2)) => (__eo_requires (__eo_eq F __eo_lv_F_2) (Term.Boolean true) (Term.Boolean false))
  | _, _ => Term.Stuck


partial def __mk_symm : Term -> Term
  | (Term.Apply (Term.Apply Term.eq t1) t2) => (Term.Apply (Term.Apply Term.eq t2) t1)
  | (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) t2)) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t2) t1))
  | _ => Term.Stuck


partial def __eo_prog_symm : Proof -> Term
  | (Proof.pf F) => (__mk_symm F)
  | _ => Term.Stuck




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
  | Stuck : CStateObj
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
  | contra : CRule
  | symm : CRule

deriving Repr, Inhabited

/-
-/
inductive CCmd : Type where
  | assume_push : Term -> CCmd
  | check_proven : Term -> CCmd
  | step : CRule -> CArgList -> CIndexList -> CCmd
  | step_pop : CRule -> CArgList -> CIndexList -> CCmd

deriving Repr, Inhabited

/-
-/
inductive CCmdList : Type where
  | nil : CCmdList
  | cons : CCmd -> CCmdList -> CCmdList
deriving Repr, Inhabited

def __eo_StateObj_proven : CStateObj -> Term
  | (CStateObj.assume F) => F
  | (CStateObj.assume_push F) => F
  | (CStateObj.proven F) => F
  | CStateObj.Stuck => Term.Stuck


def __eo_state_proven_nth : CState -> eo_lit_Int -> Term
  | (CState.cons so s), 0 => (__eo_StateObj_proven so)
  | (CState.cons so s), n => (__eo_state_proven_nth s (eo_lit_zplus n (eo_lit_zneg 1)))
  | s, n => (Term.Boolean true)


def __eo_state_is_closed : CState -> eo_lit_Bool
  | (CState.cons (CStateObj.assume_push F) s) => false
  | (CState.cons so s) => (__eo_state_is_closed s)
  | CState.nil => true
  | s => false


def __eo_push_assume : Term -> CState -> CState
  | F, s => (CState.cons (CStateObj.assume_push F) s)


def __eo_push_proven_check : Term -> Term -> CState -> CState
  | (Term.Boolean true), F, s => (CState.cons (CStateObj.proven F) s)
  | b, F, s => CState.Stuck


def __eo_push_proven : Term -> CState -> CState
  | F, s => (__eo_push_proven_check (__eo_is_ok F) F s)


def __eo_invoke_cmd_check_proven : CState -> Term -> CState
  | (CState.cons (CStateObj.proven F) S), proven => (__eo_push_proven_check (__eo_eq F proven) F S)
  | S, proven => CState.Stuck


def __eo_cmd_step_proven (S : CState) : CRule -> CArgList -> CIndexList -> Term
  | CRule.contra, CArgList.nil, (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil)) => (__eo_prog_contra (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)))
  | CRule.symm, CArgList.nil, (CIndexList.cons n1 CIndexList.nil) => (__eo_prog_symm (Proof.pf (__eo_state_proven_nth S n1)))
  | r, args, premises => Term.Stuck


def __eo_cmd_step_pop_proven (S : CState) (r : CRule) (args : CArgList) : Term -> CIndexList -> Term
  | Term.Stuck , _  => Term.Stuck
  | A, premises => Term.Stuck


def __eo_invoke_cmd_step_pop (s : CState) : CState -> CRule -> CArgList -> CIndexList -> CState
  | (CState.cons (CStateObj.assume_push A) s2), r, args, premises => (__eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) s2)
  | (CState.cons so s2), r, args, premises => (__eo_invoke_cmd_step_pop s s2 r args premises)
  | s2, r, args, premises => CState.Stuck


def __eo_invoke_cmd : CState -> CCmd -> CState
  | CState.Stuck, c => CState.Stuck
  | S, (CCmd.assume_push proven) => (__eo_push_assume proven S)
  | S, (CCmd.check_proven proven) => (__eo_invoke_cmd_check_proven S proven)
  | S, (CCmd.step r args premises) => (__eo_push_proven (__eo_cmd_step_proven S r args premises) S)
  | S, (CCmd.step_pop r args premises) => (__eo_invoke_cmd_step_pop S S r args premises)


def __eo_invoke_cmd_list (S : CState) : CCmdList -> CState
  | CCmdList.nil => S
  | (CCmdList.cons c cmds) => (__eo_invoke_cmd_list (__eo_invoke_cmd S c) cmds)


def __eo_invoke_cmd_list_assuming (S : CState) : Term -> CCmdList -> CState
  | (Term.Apply (Term.Apply Term.and F) as), cs => (__eo_invoke_cmd_list_assuming (CState.cons (CStateObj.assume F) S) as cs)
  | (Term.Boolean true), cs => (__eo_invoke_cmd_list S cs)
  | as, cs => CState.Stuck


def __eo_state_is_refutation (s : CState) : eo_lit_Bool :=
  (__eo_state_is_closed (__eo_invoke_cmd_check_proven s (Term.Boolean false)))

def __eo_checker_is_refutation : Term -> CCmdList -> eo_lit_Bool
  | as, cs => (__eo_state_is_refutation (__eo_invoke_cmd_list_assuming CState.nil as cs))





end Eo
