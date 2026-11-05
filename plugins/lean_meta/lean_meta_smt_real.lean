module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Rat.Floor
public import $EO_CALC$.SmtEval

/-!
# The real numbers of the SMT-LIB semantics

The values of sort `Real` are Mathlib's real numbers. This module, and with it
Mathlib, belongs to the verification project only: the checker computes with
`native_Rat`, the type of the rational literals of the term language, and a
literal denotes its image under `native_rat_to_real`.
-/

-- $ Not blocks of the native layer, which comes out in modules the checker
-- $ builds and is trimmed to what an input reaches. SmtValue holds a native_Real
-- $ whatever the input is, so this module is needed whatever an input reaches,
-- $ and it is what keeps the import of Mathlib to one place. It carries no
-- $ generated text. What these are in the SMT-LIB backend is said in
-- $ plugins/smt_meta/smt-vc.eos.
@[expose] public section

namespace SmtEval

abbrev native_Real := _root_.Real

-- The identifiers of the values a model is free to choose: the elements of an
-- uninterpreted sort, and functions. They are real numbers only so that there
-- are enough of them for every cardinality SMT-LIB permits; no formula can
-- observe anything about one beyond whether it equals another.
abbrev ModelId := native_Real

noncomputable section

/--
The size of a real value. What `Real` derives is constant, whereas the argument
that an infinite datatype has values of every size needs the values of a field
of sort `Real` to be of unbounded size.
-/
instance instSizeOfNativeReal : SizeOf native_Real := ⟨fun r => ⌊|r|⌋₊⟩

def native_rat_to_real : native_Rat -> native_Real
  | q => (q : _root_.Real)

def native_int_to_real : native_Int -> native_Real
  | x => (x : _root_.Real)

def native_mk_real : native_Int -> native_Int -> native_Real
  | x, y => (x : _root_.Real) / (y : _root_.Real)

def native_rplus : native_Real -> native_Real -> native_Real
  | x, y => x + y

def native_rmult : native_Real -> native_Real -> native_Real
  | x, y => x * y

def native_rneg : native_Real -> native_Real
  | x => -x

def native_rabs : native_Real -> native_Real
  | x => |x|

def native_rlt : native_Real -> native_Real -> native_Bool
  | x, y => decide (x < y)

def native_rleq : native_Real -> native_Real -> native_Bool
  | x, y => decide (x <= y)

def native_rdiv_total : native_Real -> native_Real -> native_Real
  | x, y => x / y

def native_real_to_int : native_Real -> native_Int
  | x => ⌊x⌋

end

end SmtEval
