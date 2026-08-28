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
-- the rest only this file reaches. See LeanMetaReduce::placeNativeDefs.
-- $native-place Smtm

-- The model itself, and what is asked of one. This is not of the native
-- layer: a model is what this file is about, so what stands over one is
-- written here rather than in a library the compilation trims. What the
-- embedding names -- the three lookups and the identifier a default function
-- is given -- keeps its `native_` name, since that is the name a signature
-- reaches it by; what only this file names does not.

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

-- The quantifier evaluators, which are of the model rather than of the
-- native layer: each takes one and asks what a body comes to under it,
-- which is what this file is about. They stand here for the same reason
-- the lookups above do, and keep their `native_` names because the
-- embedding names them, see $EO_TO_SMT_AUX$ in model_smt.eo.

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

def native_eval_fun_apply (M : SmtModel) (fid : native_String) (T U : SmtType) (i : SmtValue) : SmtValue :=
  let fallback := __smtx_type_default U
  if fid = native_default_fun_id then
    fallback
  else
    model_fun_lookup M fid T U i

def native_unpack_seq : SmtSeq -> List SmtValue
  | (SmtSeq.cons v vs) => v :: (native_unpack_seq vs)
  | (SmtSeq.empty _) => []

def native_pack_seq (T : SmtType) : List SmtValue -> SmtSeq
  | [] => (SmtSeq.empty T)
  | v :: vs => (SmtSeq.cons v (native_pack_seq T vs))

def native_ssm_char_of_value : SmtValue -> native_Char
  | (SmtValue.Char c) => c
  | _ => 0

def native_unpack_string (x : SmtSeq) : native_String :=
  (native_unpack_seq x).map native_ssm_char_of_value

def native_pack_string (s : native_String) : SmtSeq :=
  native_pack_seq SmtType.Char (s.map SmtValue.Char)

def native_seq_len : List SmtValue -> native_Int
  | x => Int.ofNat x.length

def native_seq_concat : List SmtValue -> List SmtValue -> List SmtValue
  | x, y => x ++ y

def native_seq_extract (xs : List SmtValue) (i : native_Int) (n : native_Int) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || n <= 0 || i >= len then
    []
  else
    let start : Nat := Int.toNat i
    let take : Nat := Int.toNat (min n (len - i))
    (xs.drop start).take take

/-- Generic sequence pattern operations share the regular expression matcher.
These small adapters also give the SMT backend distinct entry points that it
can map directly to the corresponding polymorphic `seq.*` operators. -/
def native_seq_indexof (xs pat : List SmtValue) (i : native_Int) : native_Int :=
  native_str_indexof_re xs (native_str_to_re pat) i

def native_seq_contains (xs pat : List SmtValue) : native_Bool :=
  0 <= native_seq_indexof xs pat 0

def native_seq_replace (xs pat repl : List SmtValue) : List SmtValue :=
  native_str_replace_re xs (native_str_to_re pat) repl

def native_seq_replace_all (xs pat repl : List SmtValue) : List SmtValue :=
  native_str_replace_re_all xs (native_str_to_re pat) repl

def native_seq_occur_index (xs pat : List SmtValue) (n : native_Int) : native_Int :=
  native_str_occur_index_re xs (native_str_to_re pat) n

def native_seq_update (xs : List SmtValue) (i : native_Int) (ys : List SmtValue) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || len <= i then
    xs
  else
    let idx := Int.toNat i
    (xs.take idx) ++ (ys.take (xs.length - idx)) ++
      (xs.drop (idx + ys.length))

def native_seq_rev : List SmtValue -> List SmtValue
  | xs => xs.reverse

end

end

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
