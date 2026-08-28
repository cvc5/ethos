module

public import $EO_CALC$.SmtModelDefs
import all $EO_CALC$.SmtModelDefs

public section

set_option linter.unusedVariables false

namespace Smtm

open SmtEval

/-
A total order on SMT-LIB values.

Values are mapped to a generic key (a binary tree of natural numbers) by
the mutually recursive *Key methods below, which are generated from the
constructors of the deeply embedded datatypes. A constructor whose index
in its datatype is `n` and whose arguments have keys `k1 ... kj` is
mapped to `node n [k1, ..., kj]`. The order on values is then the
lexicographic order on keys, given by Key.lt.

The key method for an argument is found by name: it is the name of the
argument's type with the Smt or native_ prefix dropped, its first letter
lowercased and Key appended, e.g. datatypeDeclKey orders SmtDatatypeDecl
and intKey orders native_Int. Every type that can occur as an argument of
a value or type constructor must therefore have a method of that name,
either generated below or given here.
-/
namespace SmtValueOrder

inductive Key where
  | atom : Nat → Key
  | pair : Key → Key → Key
deriving DecidableEq, Repr

@[expose] def Key.lt : Key → Key → Bool
  | .atom m, .atom n => decide (m < n)
  | .atom _, .pair _ _ => true
  | .pair _ _, .atom _ => false
  | .pair a b, .pair c d => if a = c then Key.lt b d else Key.lt a c
termination_by a b => sizeOf a + sizeOf b

@[expose] def fields : List Key → Key
  | [] => .atom 0
  | k :: ks => .pair k (fields ks)

@[expose] def node (tag : Nat) (ks : List Key) : Key :=
  .pair (.atom tag) (fields ks)

@[expose] def natKey (n : Nat) : Key := .atom n

@[expose] def boolKey : Bool → Key
  | false => .atom 0
  | true => .atom 1

@[expose] def intKey : Int → Key
  | .ofNat n => node 0 [natKey n]
  | .negSucc n => node 1 [natKey n]

@[expose] def ratKey (q : Rat) : Key :=
  node 0 [intKey q.num, natKey q.den]

@[expose] def charKey (c : native_Char) : Key := .atom c

@[expose] def stringKey : native_String → Key
  | [] => .atom 0
  | c :: cs => .pair (charKey c) (stringKey cs)

mutual

@[expose] def typeKey : SmtType -> Key
$LEAN_SMT_TYPE_KEY$
@[expose] def valueKey : SmtValue -> Key
$LEAN_SMT_VALUE_KEY$
@[expose] def regLanKey : SmtRegLan -> Key
  | .empty => node 0 []
  | .epsilon => node 1 []
  | .char c => node 2 [valueKey c]
  | .range lo hi => node 3 [valueKey lo, valueKey hi]
  | .allchar => node 4 []
  | .concat r₁ r₂ => node 5 [regLanKey r₁, regLanKey r₂]
  | .union r₁ r₂ => node 6 [regLanKey r₁, regLanKey r₂]
  | .inter r₁ r₂ => node 7 [regLanKey r₁, regLanKey r₂]
  | .star r => node 8 [regLanKey r]
  | .comp r => node 9 [regLanKey r]

@[expose] def mapKey : SmtMap -> Key
  | .cons i e m => node 0 [valueKey i, valueKey e, mapKey m]
  | .default t e => node 1 [typeKey t, valueKey e]

@[expose] def seqKey : SmtSeq -> Key
  | .cons v vs => node 0 [valueKey v, seqKey vs]
  | .empty t => node 1 [typeKey t]

@[expose] def datatypeDeclKey : SmtDatatypeDecl -> Key
  | .nil => node 0 []
  | .cons s d dd => node 1 [stringKey s, datatypeKey d, datatypeDeclKey dd]

@[expose] def datatypeKey : SmtDatatype -> Key
  | .null => node 0 []
  | .sum c d => node 1 [datatypeConsKey c, datatypeKey d]

@[expose] def datatypeConsKey : SmtDatatypeCons -> Key
  | .unit => node 0 []
  | .cons t c => node 1 [typeKey t, datatypeConsKey c]

end

@[expose] def lt (a b : SmtValue) : Bool := Key.lt (valueKey a) (valueKey b)

end SmtValueOrder

-- The comparison of two values, which is the order above under the name the
-- embedding gives it.

-- $native native_vcmp
/- Value comparison -/
def native_vcmp (v1 : SmtValue) (v2 : SmtValue) : native_Bool :=
  SmtValueOrder.lt v1 v2
-- $native-end

end Smtm
