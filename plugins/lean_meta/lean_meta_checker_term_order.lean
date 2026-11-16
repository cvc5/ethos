module

public import $EO_CALC$.LogosTerm
import all $EO_CALC$.LogosTerm

public section

namespace Eo

open SmtEval

-- $ The order on Eunoia terms native_tcmp is. It is written out rather than
-- $ derived (`deriving Ord`) so that a proof can unfold it: a derived instance
-- $ is opaque to the kernel's reduction in the ways a proof about the sort the
-- $ checker performs needs. The UserOp<n> comparisons and the cases of termCmp
-- $ are generated, one per inductive and constructor LogosTerm declares, see
-- $ LeanMetaReduce::printTermOrder; the rest is fixed, since DatatypeDecl,
-- $ Datatype and DatatypeCons are fixed in LogosTerm too.
/-
A total order on Eunoia terms, used by the checker to sort (e.g. the
monomials of a polynomial normal form). It is lexicographic: constructor
index first, then the arguments left to right. It is defined by structural
recursion and exposed, so that proofs can unfold it. Each argument type
`T` is compared by the method named after it (natCmp for native_Nat,
termCmp for Term, ...); user operators are compared by constructor index.
Rationals are ordered by (numerator, denominator), which is a total order
on reduced fractions but not the numeric one.
-/
@[expose] def natCmp (a b : native_Nat) : Ordering :=
  if a < b then .lt else if a = b then .eq else .gt

@[expose] def intCmp (a b : native_Int) : Ordering :=
  if a < b then .lt else if a = b then .eq else .gt

@[expose] def boolCmp : native_Bool -> native_Bool -> Ordering
  | false, true => .lt
  | true, false => .gt
  | _, _ => .eq

@[expose] def ratCmp (a b : native_Rat) : Ordering :=
  match intCmp a.num b.num with
  | .eq => natCmp a.den b.den
  | o => o

@[expose] def stringCmp : native_String -> native_String -> Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | c :: s, d :: t =>
    match natCmp c d with
    | .eq => stringCmp s t
    | o => o

$LEAN_EO_USER_OP_CMPS$

mutual

@[expose] def termCmp : Term -> Term -> Ordering
$LEAN_TERM_CMP$
termination_by structural a _ => a

@[expose] def datatypeDeclCmp : DatatypeDecl -> DatatypeDecl -> Ordering
  | .nil, b => natCmp (DatatypeDecl.ctorIdx .nil) b.ctorIdx
  | a@(.cons x1 x2 x3), b =>
    match b with
    | .cons y1 y2 y3 =>
      match stringCmp x1 y1 with
      | .eq =>
        match datatypeCmp x2 y2 with
        | .eq =>
          datatypeDeclCmp x3 y3
        | o => o
      | o => o
    | _ => natCmp a.ctorIdx b.ctorIdx
termination_by structural a _ => a

@[expose] def datatypeCmp : Datatype -> Datatype -> Ordering
  | .null, b => natCmp (Datatype.ctorIdx .null) b.ctorIdx
  | a@(.sum x1 x2), b =>
    match b with
    | .sum y1 y2 =>
      match datatypeConsCmp x1 y1 with
      | .eq =>
        datatypeCmp x2 y2
      | o => o
    | _ => natCmp a.ctorIdx b.ctorIdx
termination_by structural a _ => a

@[expose] def datatypeConsCmp : DatatypeCons -> DatatypeCons -> Ordering
  | .unit, b => natCmp (DatatypeCons.ctorIdx .unit) b.ctorIdx
  | a@(.cons x1 x2), b =>
    match b with
    | .cons y1 y2 =>
      match termCmp x1 y1 with
      | .eq =>
        datatypeConsCmp x2 y2
      | o => o
    | _ => natCmp a.ctorIdx b.ctorIdx
termination_by structural a _ => a

end

/- Term less than, based on the order termCmp above -/
@[expose] def native_tcmp (a b : Term) : native_Bool :=
  match termCmp a b with
  | Ordering.lt => true
  | _ => false

end Eo
