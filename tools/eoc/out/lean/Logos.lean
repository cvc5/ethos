import Cpc.SmtEval

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Eo

open SmtEval

/- Eunoia literal evaluation defined -/

def native_str_len : native_String -> native_Int
  | x => Int.ofNat x.length
def native_str_concat : native_String -> native_String -> native_String
  | x, y => x ++ y
def native_str_substr (s : native_String) (i n : native_Int) : native_String :=
  let len : Int := (native_str_len s)
  if i < 0 || n <= 0 || i >= len then
    ""
  else
    let start : Nat := Int.toNat i
    let take  : Nat := Int.toNat (min n (len - i))
    String.Pos.Raw.extract s ⟨start⟩ ⟨start + take⟩
def native_str_indexof_rec (s t : native_String) (i len fuel : Nat) : native_Int :=
  match fuel with
  | 0 => -1
  | fuel + 1 =>
      if String.Pos.Raw.substrEq s ⟨i⟩ t ⟨0⟩ len then
        i
      else
        native_str_indexof_rec s t (i + 1) len fuel
def native_str_indexof (s t : native_String) (i : native_Int) : native_Int :=
  if i < 0 then
    -1
  else
    let sLen := Int.toNat (native_str_len s)
    let start := Int.toNat i
    let tLen := Int.toNat (native_str_len t)
    if h : start + tLen <= sLen then
      native_str_indexof_rec s t start tLen (sLen - (start + tLen) + 1)
    else
      -1

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
  | __eo_List : Term
  | __eo_List_nil : Term
  | __eo_List_cons : Term
  | Bool : Term
  | Boolean : native_Bool -> Term
  | Numeral : native_Int -> Term
  | Rational : native_Rat -> Term
  | String : native_String -> Term
  | Binary : native_Int -> native_Int -> Term
  | Type : Term
  | Stuck : Term
  | Apply : Term -> Term -> Term
  | FunType : Term
  | Var : Term -> Term -> Term
  | DatatypeType : native_String -> Datatype -> Term
  | DatatypeTypeRef : native_String -> Term
  | DtCons : native_String -> Datatype -> native_Nat -> Term
  | DtSel : native_String -> Datatype -> native_Nat -> native_Nat -> Term
  | USort : native_Nat -> Term
  | UConst : native_Nat -> Term -> Term
  | not : Term
  | or : Term
  | and : Term
  | imp : Term
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
def native_teq : Term -> Term -> native_Bool
  | x, y => decide (x = y)

/- Term less than, based on arbitrary ordering -/
def native_tcmp (a b : Term) : native_Bool :=
  match compare a b with
  | Ordering.lt => true
  | _ => false

/- Used for defining hash -/
def native_thash : Term -> native_Int
  | _ => 0 -- FIXME

/- Proofs -/
inductive Proof : Type where
  | pf : Term -> Proof
  | Stuck : Proof

/- Definition of Eunoia signature -/

mutual

def __eo_mk_apply : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | x1, x2 => (Term.Apply x1 x2)


def __eo_binary_mod_w (w : native_Int) (n : native_Int) : Term :=
  (Term.Binary w (native_mod_total n (native_int_pow2 w)))

def __eo_ite : Term -> Term -> Term -> Term
  | x1, x2, x3 => (native_ite (native_teq x1 (Term.Boolean true)) x2 (native_ite (native_teq x1 (Term.Boolean false)) x3 Term.Stuck))


def __eo_requires : Term -> Term -> Term -> Term
  | x1, x2, x3 => (native_ite (native_teq x1 x2) (native_ite (native_not (native_teq x1 Term.Stuck)) x3 Term.Stuck) Term.Stuck)


def __eo_and : Term -> Term -> Term
  | (Term.Boolean b1), (Term.Boolean b2) => (Term.Boolean (native_and b1 b2))
  | (Term.Binary w1 n1), (Term.Binary w2 n2) => 
    let _v0 := (Term.Numeral w1)
    (native_ite (native_teq _v0 (Term.Numeral w2)) (native_ite (native_not (native_teq _v0 Term.Stuck)) (Term.Binary w1 (native_mod_total (native_binary_and w1 n1 n2) (native_int_pow2 w1))) Term.Stuck) Term.Stuck)
  | _, _ => Term.Stuck


def __eo_len : Term -> Term
  | (Term.String s1) => (Term.Numeral (native_str_len s1))
  | (Term.Binary w n1) => (Term.Numeral w)
  | _ => Term.Stuck


def __eo_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | t, s => (Term.Boolean (native_teq s t))


def __eo_dtc_substitute (s : native_String) (d : Datatype) : DatatypeCons -> DatatypeCons
  | (DatatypeCons.cons (Term.DatatypeType s2 d2) c) => (DatatypeCons.cons (Term.DatatypeType s2 (native_ite (native_streq s s2) d2 (__eo_dt_substitute s d d2))) (__eo_dtc_substitute s d c))
  | (DatatypeCons.cons T c) => (DatatypeCons.cons (native_ite (native_teq T (Term.DatatypeTypeRef s)) (Term.DatatypeType s d) T) (__eo_dtc_substitute s d c))
  | DatatypeCons.unit => DatatypeCons.unit


def __eo_dt_substitute (s : native_String) (d : Datatype) : Datatype -> Datatype
  | (Datatype.sum c d2) => (Datatype.sum (__eo_dtc_substitute s d c) (__eo_dt_substitute s d d2))
  | Datatype.null => Datatype.null


def __eo_is_bool_type : Term -> Term
  | Term.Stuck  => Term.Stuck
  | x => (__eo_eq (__eo_typeof x) Term.Bool)


def __eo_prog_contra : Proof -> Proof -> Term
  | (Proof.pf F), (Proof.pf (Term.Apply Term.not __eo_lv_F_2)) => (__eo_requires (__eo_eq F __eo_lv_F_2) (Term.Boolean true) (Term.Boolean false))
  | _, _ => Term.Stuck


def __mk_symm : Term -> Term
  | (Term.Apply (Term.Apply Term.eq t1) t2) => (Term.Apply (Term.Apply Term.eq t2) t1)
  | (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t1) t2)) => (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq t2) t1))
  | _ => Term.Stuck


def __eo_prog_symm : Proof -> Term
  | (Proof.pf F) => (__mk_symm F)
  | _ => Term.Stuck


def __eo_typeof_dt_cons_rec : Term -> Datatype -> native_Nat -> Term
  | Term.Stuck , _ , _  => Term.Stuck
  | T, (Datatype.sum DatatypeCons.unit d), native_nat_zero => T
  | T, (Datatype.sum (DatatypeCons.cons U c) d), native_nat_zero => (Term.Apply (Term.Apply Term.FunType U) (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero))
  | T, (Datatype.sum c d), (native_nat_succ n) => (__eo_typeof_dt_cons_rec T d n)
  | _, _, _ => Term.Stuck


def __eo_typeof_dt_sel_return : Datatype -> native_Nat -> native_Nat -> Term
  | (Datatype.sum (DatatypeCons.cons T c) d), native_nat_zero, native_nat_zero => T
  | (Datatype.sum (DatatypeCons.cons T c) d), native_nat_zero, (native_nat_succ m) => (__eo_typeof_dt_sel_return (Datatype.sum c d) native_nat_zero m)
  | (Datatype.sum c d), (native_nat_succ n), m => (__eo_typeof_dt_sel_return d n m)
  | _, _, _ => Term.Stuck


def __eo_typeof_apply : Term -> Term -> Term
  | _ , Term.Stuck  => Term.Stuck
  | (Term.Apply (Term.Apply Term.FunType T) U), V => (__eo_requires T V U)
  | _, _ => Term.Stuck


def __eo_typeof_fun_type : Term -> Term -> Term
  | Term.Type, Term.Type => Term.Type
  | _, _ => Term.Stuck


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


def __eo_typeof_BitVec : Term -> Term
  | Term.Int => Term.Type
  | _ => Term.Stuck


def __eo_typeof_Seq : Term -> Term
  | Term.Type => Term.Type
  | _ => Term.Stuck


def __eo_typeof_not : Term -> Term
  | Term.Bool => Term.Bool
  | _ => Term.Stuck


def __eo_typeof_or : Term -> Term -> Term
  | Term.Bool, Term.Bool => Term.Bool
  | _, _ => Term.Stuck


def __eo_typeof_eq : Term -> Term -> Term
  | Term.Stuck , _  => Term.Stuck
  | _ , Term.Stuck  => Term.Stuck
  | A, __eo_lv_A_2 => (__eo_requires (__eo_eq A __eo_lv_A_2) (Term.Boolean true) Term.Bool)


def __eo_typeof : Term -> Term
  | (Term.Boolean b) => Term.Bool
  | (Term.Numeral n) => (__eo_lit_type_Numeral (Term.Numeral n))
  | (Term.Rational r) => (__eo_lit_type_Rational (Term.Rational r))
  | (Term.String s) => (__eo_lit_type_String (Term.String s))
  | (Term.Binary w n) => (__eo_lit_type_Binary (Term.Binary w n))
  | (Term.Var (Term.String s) T) => T
  | (Term.DatatypeType s d) => Term.Type
  | (Term.DatatypeTypeRef s) => Term.Type
  | (Term.DtCons s d i) => (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) (__eo_dt_substitute s d d) i)
  | (Term.DtSel s d i j) => (Term.Apply (Term.Apply Term.FunType (Term.DatatypeType s d)) (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j))
  | (Term.USort i) => Term.Type
  | (Term.UConst i T) => T
  | Term.Type => Term.Type
  | (Term.Apply (Term.Apply Term.FunType __eo_T) __eo_U) => (__eo_typeof_fun_type (__eo_typeof __eo_T) (__eo_typeof __eo_U))
  | Term.Bool => Term.Type
  | Term.__eo_List => Term.Type
  | Term.__eo_List_nil => Term.__eo_List
  | (Term.Apply Term.__eo_List_cons __eo_x1) => (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
  | Term.Int => Term.Type
  | Term.Real => Term.Type
  | (Term.Apply Term.BitVec __eo_x1) => (__eo_typeof_BitVec (__eo_typeof __eo_x1))
  | Term.Char => Term.Type
  | (Term.Apply Term.Seq __eo_x1) => (__eo_typeof_Seq (__eo_typeof __eo_x1))
  | (Term.Apply Term.not __eo_x1) => (__eo_typeof_not (__eo_typeof __eo_x1))
  | (Term.Apply (Term.Apply Term.or __eo_x1) __eo_x2) => (__eo_typeof_or (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.and __eo_x1) __eo_x2) => (__eo_typeof_or (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.imp __eo_x1) __eo_x2) => (__eo_typeof_or (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply (Term.Apply Term.eq __eo_x1) __eo_x2) => (__eo_typeof_eq (__eo_typeof __eo_x1) (__eo_typeof __eo_x2))
  | (Term.Apply __eo_f __eo_x) => (__eo_typeof_apply (__eo_typeof __eo_f) (__eo_typeof __eo_x))
  | _ => Term.Stuck


end





/- Definition of the checker -/

abbrev CIndex := native_Int

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


def __eo_state_proven_nth : CState -> native_Int -> Term
  | (CState.cons so s), 0 => (__eo_StateObj_proven so)
  | (CState.cons so s), n => (__eo_state_proven_nth s (native_zplus n (native_zneg 1)))
  | s, n => (Term.Boolean true)


def __eo_state_is_closed : CState -> native_Bool
  | (CState.cons (CStateObj.assume_push F) s) => false
  | (CState.cons so s) => (__eo_state_is_closed s)
  | CState.nil => true
  | s => false


def __eo_push_assume_check : Term -> Term -> CState -> CState
  | (Term.Boolean true), F, s => (CState.cons (CStateObj.assume_push F) s)
  | b, F, s => CState.Stuck


def __eo_push_assume : Term -> CState -> CState
  | F, s => (__eo_push_assume_check (__eo_is_bool_type F) F s)


def __eo_push_proven_check : Term -> Term -> CState -> CState
  | (Term.Boolean true), F, s => (CState.cons (CStateObj.proven F) s)
  | b, F, s => CState.Stuck


def __eo_push_proven : Term -> CState -> CState
  | F, s => (__eo_push_proven_check (__eo_is_bool_type F) F s)


def __eo_invoke_cmd_check_proven : CState -> Term -> CState
  | (CState.cons (CStateObj.proven F) S), proven => (__eo_push_proven_check (__eo_eq F proven) F S)
  | S, proven => CState.Stuck


def __eo_cmd_step_proven (S : CState) : CRule -> CArgList -> CIndexList -> Term
  | CRule.contra, CArgList.nil, (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil)) => (__eo_prog_contra (Proof.pf (__eo_state_proven_nth S n1)) (Proof.pf (__eo_state_proven_nth S n2)))
  | CRule.symm, CArgList.nil, (CIndexList.cons n1 CIndexList.nil) => (__eo_prog_symm (Proof.pf (__eo_state_proven_nth S n1)))
  | r, args, premises => Term.Stuck


def __eo_cmd_step_pop_proven (S : CState) (r : CRule) (args : CArgList) : Term -> CIndexList -> Term
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


def __eo_state_is_refutation (s : CState) : native_Bool :=
  (__eo_state_is_closed (__eo_invoke_cmd_check_proven s (Term.Boolean false)))

def __eo_invoke_assume_list (S : CState) : Term -> CState
  | (Term.Apply (Term.Apply Term.and F) as) => (CState.cons (CStateObj.assume F) (__eo_invoke_assume_list S as))
  | (Term.Boolean true) => S
  | as => CState.Stuck


def __eo_checker_is_refutation : Term -> CCmdList -> native_Bool
  | as, cs => (__eo_state_is_refutation (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil as) cs))




/-- API for logos -/
def logos_init_state : CState := CState.nil
def logos_invoke_assume (s : CState) (A : Term) : CState := (CState.cons (CStateObj.assume A) s)
def logos_invoke_cmd (s : CState) (c :CCmd) : CState := (__eo_invoke_cmd s c)
def logos_state_is_refutation (s : CState) : native_Bool := (__eo_state_is_refutation s)

end Eo
