module

public import $EO_CALC$.LogosTerm
import all $EO_CALC$.LogosTerm
public import $EO_CALC$.SmtEval
import all $EO_CALC$.SmtEval

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Eo

open SmtEval

/- Eunoia literal evaluation defined -/

/- Term ITE -/
abbrev __eo_ite (x1 : Term) (x2 : Term) (x3 : Term) : Term :=
  (native_ite (native_teq x1 (Term.Boolean true))
    x2
    (native_ite (native_teq x1 (Term.Boolean false))
      x3
      Term.Stuck))

/- Proofs -/
inductive Proof : Type where
  | pf : Term -> Proof
  | Stuck : Proof

/- Definition of Eunoia signature -/

$LEAN_DEFS_TOTAL$

$LEAN_DEFS$

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

/- Definition of refutation -/
inductive eo_is_refutation : Term -> CCmdList -> Prop
$LEAN_EO_IS_REFUTATION_DEF$

end Eo
