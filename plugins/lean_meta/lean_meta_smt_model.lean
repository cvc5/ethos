module

public import Mathlib.Data.Set.Finite.Basic
public import $EO_CALC$.SmtTyping
import all $EO_CALC$.SmtTyping
public import $EO_CALC$.SmtValueOrder
import all $EO_CALC$.SmtValueOrder

@[expose] public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

noncomputable section

abbrev SmtNativeFun := SmtValue -> SmtValue

-- The identifiers of each uninterpreted sort, by its index: the sort's values
-- are exactly the `UValue`s with one of them, so its cardinality is the size of
-- the set. `model_wf` says which sets a model may choose.
abbrev SmtUSortDom := native_Nat -> _root_.Set ModelId

-- The primitive operations no module above this one uses, together with those
-- written over the values of this embedding, which cannot stand above it.
-- $ The part of the native layer whose Lean names the embedding, and the part
-- $ no module above this one reaches, see LeanMetaReduce::nativeDefs.
$NATIVE_DEFS$

-- The model itself, and what is asked of one: what a symbol is interpreted
-- as, the two lookups a term is evaluated with, the push a binder makes, and
-- the identifier a default function is given.
-- $ Not of the native layer: a model is what this file is about, so what
-- $ stands over one is written here rather than in lean.eos, which the
-- $ compilation trims to what an input reaches. What the embedding names
-- $ keeps its `native_` name, since that is the name a signature reaches it
-- $ by; what only this file names does not, which is why model_key and
-- $ model_fun_lookup are spelled without it.

structure SmtModelKey where
  isVar : native_Bool
  name : native_String
  ty : SmtType
deriving Repr, DecidableEq, Inhabited

structure SmtModel where
  values : SmtModelKey -> SmtValue
  nativeFuns : ModelId -> SmtType -> SmtType -> SmtNativeFun
  usortDom : SmtUSortDom
deriving Inhabited

def model_key (s : native_String) (T : SmtType) : SmtModelKey :=
  { isVar := false, name := s, ty := T }

def model_fun_lookup (M : SmtModel) (fid : ModelId) (T U : SmtType) : SmtNativeFun :=
  M.nativeFuns fid T U

def native_default_fun_id : ModelId := 0

def native_model_var_lookup (M : SmtModel) (s : native_String) (T : SmtType) : SmtValue :=
  M.values { isVar := true, name := s, ty := T }

def native_model_lookup (M : SmtModel) (s : native_String) (T : SmtType) : SmtValue :=
  M.values (model_key s T)

def native_model_push (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) : SmtModel :=
  { M with values := fun k =>
      if k = { isVar := true, name := s, ty := T } then
        v
      else
        M.values k }

open Classical in
def native_usort_mem (uc : SmtUSortDom) (n : native_Nat) (r : ModelId) : native_Bool :=
  decide (r ∈ uc n)

open Classical in
def native_usort_finite (uc : SmtUSortDom) (n : native_Nat) : native_Bool :=
  decide (uc n).Finite

open Classical in
def native_usort_unit (uc : SmtUSortDom) (n : native_Nat) : native_Bool :=
  decide (uc n = {0})

/- Definition of SMT-LIB model semantics -/

mutual

$LEAN_SMT_EVAL_DEFS$

def native_eval_fun_apply (M : SmtModel) (fid : ModelId) (T U : SmtType) (i : SmtValue) : SmtValue :=
  let fallback := __smtx_type_default U
  if fid = native_default_fun_id then
    fallback
  else
    model_fun_lookup M fid T U i

end

$LEAN_SMT_EVAL$

def model_fun_wf (M : SmtModel) : Prop :=
  ∀ fid A B i,
    __smtx_type_wf (SmtType.FunType A B) = true ->
    __smtx_typeof_value i = A ->
    __smtx_typeof_value (native_eval_fun_apply M fid A B i) = B ∧
      __smtx_value_canonical M.usortDom (native_eval_fun_apply M fid A B i) = true

-- Every sort has the value `UValue _ 0`, which is its default, and an infinite
-- sort has identifiers of arbitrarily large `sizeOf`. Identifiers are only labels,
-- so this rules out no cardinality up to the size of `Real`.
def usort_dom_wf (uc : SmtUSortDom) : Prop :=
  ∀ i, (0 : ModelId) ∈ uc i ∧
    ((uc i).Infinite -> ∀ n : native_Nat, ∃ r ∈ uc i, (n : ModelId) ≤ |r|)

def model_wf (M : SmtModel) : Prop :=
  (∀ isVar s T, __smtx_type_wf T = true ->
    __smtx_typeof_value (M.values { isVar := isVar, name := s, ty := T }) = T) ∧
  (∀ isVar s T, __smtx_type_wf T = true ->
    __smtx_value_canonical M.usortDom
      (M.values { isVar := isVar, name := s, ty := T }) = true) ∧
  model_fun_wf M ∧
  usort_dom_wf M.usortDom

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_satisfiability : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, model_wf M /\ (__smtx_model_eval M t) = (SmtValue.Boolean true)) ->
      smt_satisfiability t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, model_wf M -> (__smtx_model_eval M t) = (SmtValue.Boolean false))->
      smt_satisfiability t false

/- ---------------------------------------------- -/

end

end Smtm
