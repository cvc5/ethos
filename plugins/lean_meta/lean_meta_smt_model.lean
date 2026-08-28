module

public import $EO_CALC$.SmtValueOrder
import all $EO_CALC$.SmtValueOrder

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

abbrev SmtNativeFun := SmtValue -> SmtValue

-- The part of the native layer that the SMT-LIB value embedding is what
-- decides, and so cannot come out above this file, together with whatever of
-- the rest only this file reaches.
-- $native-place Smtm

-- The model itself, and what is asked of one. This is not of the native
-- layer: a model is what this file is about, so what stands over one is
-- written here rather than in a library the compilation trims. What the
-- embedding names keeps its `native_` name, since that is the name a
-- signature reaches it by: the two lookups, the push, and the identifier a
-- default function is given. What only this file names does not, which is
-- why model_key and model_fun_lookup are spelled without it.

structure SmtModelKey where
  isVar : native_Bool
  name : native_String
  ty : SmtType
deriving Repr, DecidableEq, Inhabited

structure SmtModel where
  values : SmtModelKey -> SmtValue
  nativeFuns : SmtModelKey -> SmtNativeFun
deriving Inhabited

def model_key (s : native_String) (T : SmtType) : SmtModelKey :=
  { isVar := false, name := s, ty := T }

def model_fun_lookup (M : SmtModel) (fid : native_String) (T U : SmtType) : SmtNativeFun :=
  M.nativeFuns (model_key fid (SmtType.FunType T U))

def native_default_fun_id : native_String := (native_string_lit "@native_default_fun")

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

/- Definition of SMT-LIB model semantics -/

noncomputable section

mutual

def native_inhabited_type (T : SmtType) : native_Bool :=
  (native_and
    (native_not (native_Teq T SmtType.None))
    (native_Teq (__smtx_typeof_value (__smtx_type_default T)) T))

$LEAN_SMT_EVAL_DEFS$

def native_eval_fun_apply (M : SmtModel) (fid : native_String) (T U : SmtType) (i : SmtValue) : SmtValue :=
  let fallback := __smtx_type_default U
  if fid = native_default_fun_id then
    fallback
  else
    model_fun_lookup M fid T U i

end

end

-- The quantifier evaluators, which are of the model rather than of the native
-- layer: each takes a model and asks what a body comes to under it, which is
-- what this file is about. They stand after the mutual block above rather
-- than beside what they reach: a macro_rules is neither a definition nor an
-- inductive, so a mutual block holding one is rejected whole. Nothing is lost
-- by standing here, since they reach the evaluator through Lean.mkIdent and
-- their one use site is below. They keep their `native_` names because the
-- embedding names them.

macro_rules
  | `(native_eval_texists $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `native_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      let canonId := Lean.mkIdent `__smtx_value_canonical
      `(by
          classical
          exact
            if h :
                ∃ v : SmtValue,
                  $typeofValueId v = $T ∧
                    $canonId v = true ∧
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              SmtValue.Boolean true
            else
              SmtValue.Boolean false)

macro_rules
  | `(native_eval_tforall $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `native_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      let canonId := Lean.mkIdent `__smtx_value_canonical
      `(by
          classical
          exact
            if h :
                ∀ v : SmtValue,
                  $typeofValueId v = $T ->
                    $canonId v = true ->
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              SmtValue.Boolean true
            else
              SmtValue.Boolean false)

macro_rules
  | `(native_eval_tchoice $M $s $T $body) => do
      let evalId := Lean.mkIdent `__smtx_model_eval
      let pushId := Lean.mkIdent `native_model_push
      let typeofValueId := Lean.mkIdent `__smtx_typeof_value
      let canonId := Lean.mkIdent `__smtx_value_canonical
      `(by
          classical
          exact
            if hSat :
                ∃ v : SmtValue,
                  $typeofValueId v = $T ∧
                    $canonId v = true ∧
                    $evalId ($pushId $M $s $T v) $body = (SmtValue.Boolean true) then
              Classical.choose hSat
            else if hTy : ∃ v : SmtValue, $typeofValueId v = $T ∧ $canonId v then
              Classical.choose hTy
            else
              SmtValue.NotValue)

$LEAN_SMT_EVAL$

def model_fun_wf (M : SmtModel) : Prop :=
  ∀ fid A B i,
    __smtx_type_wf (SmtType.FunType A B) = true ->
    __smtx_typeof_value i = A ->
    __smtx_typeof_value (native_eval_fun_apply M fid A B i) = B ∧
      __smtx_value_canonical (native_eval_fun_apply M fid A B i) = true

def model_wf (M : SmtModel) : Prop :=
  (∀ isVar s T, __smtx_type_wf T = true ->
    __smtx_typeof_value (M.values { isVar := isVar, name := s, ty := T }) = T) ∧
  (∀ isVar s T, __smtx_type_wf T = true ->
    __smtx_value_canonical
      (M.values { isVar := isVar, name := s, ty := T }) = true) ∧
  model_fun_wf M

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

end Smtm
