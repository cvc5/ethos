module

public import $EO_CALC$.SmtEval
import all $EO_CALC$.SmtEval

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Eo

open SmtEval

/-
Ordinary user operators.
-/
inductive UserOp : Type where
$LEAN_EO_THEORY_OP_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/-
User operators with one index.
-/
inductive UserOp1 : Type where
$LEAN_EO_THEORY_OP1_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/-
User operators with two indices.
-/
inductive UserOp2 : Type where
$LEAN_EO_THEORY_OP2_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/-
User operators with three indices.
-/
inductive UserOp3 : Type where
$LEAN_EO_THEORY_OP3_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

mutual

/- Term definition -/
inductive Term : Type where
$LEAN_TERM_DEF$
deriving Repr, DecidableEq, Inhabited, Ord

/-
Eunoia datatype declarations.
-/
inductive DatatypeDecl : Type where
  | nil : DatatypeDecl
  | cons : native_String -> Datatype -> DatatypeDecl -> DatatypeDecl
deriving Repr, DecidableEq, Inhabited, Ord

/-
Eunoia datatypes.
-/
inductive Datatype : Type where
  | null : Datatype
  | sum : DatatypeCons -> Datatype -> Datatype
deriving Repr, DecidableEq, Inhabited, Ord

/-
Eunoia datatype constructors.
-/
inductive DatatypeCons : Type where
  | unit : DatatypeCons
  | cons : Term -> DatatypeCons -> DatatypeCons
deriving Repr, DecidableEq, Inhabited, Ord

end

/- Term equality -/
def native_teq : Term -> Term -> native_Bool
  | x, y => decide (x = y)

end Eo
