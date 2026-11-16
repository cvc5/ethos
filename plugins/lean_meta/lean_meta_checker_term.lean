module

public import $EO_CALC$.SmtEval
import all $EO_CALC$.SmtEval

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Eo

open SmtEval

-- $ The user operators, one inductive per index arity the signature uses:
-- $ UserOp for the operators that take no index and UserOp<n> for those that
-- $ take n. An arity the signature does not use gets no inductive, since Term
-- $ has no constructor that would name one. See printTheoryOpDefs.
$LEAN_EO_THEORY_OP_DEFS$

mutual

/- Term definition -/
inductive Term : Type where
$LEAN_TERM_DEF$
deriving Repr, DecidableEq, Inhabited

/-
Eunoia datatype declarations.
-/
inductive DatatypeDecl : Type where
  | nil : DatatypeDecl
  | cons : native_String -> Datatype -> DatatypeDecl -> DatatypeDecl
deriving Repr, DecidableEq, Inhabited

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

-- Equality of Eunoia terms, which the checker asks for and the Term inductive
-- above is what decides. It stands after the mutual block rather than beside
-- the inductive whose `deriving` makes it possible: a mutual block holds
-- inductives or definitions, never both. The order on terms, native_tcmp, is
-- defined in LogosTermOrder.

/- Term equality -/
def native_teq : Term -> Term -> native_Bool
  | x, y => decide (x = y)

end Eo
