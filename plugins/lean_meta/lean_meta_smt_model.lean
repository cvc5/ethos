module

public import $EO_CALC$.SmtValueOrder
import all $EO_CALC$.SmtValueOrder

public section

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

open SmtEval

abbrev SmtNativeFun := SmtValue -> SmtValue

-- A datatype declaration is checked against the list of references it may
-- name, which only the published tree builds, so the list is kept whatever
-- this compilation reaches.
-- $native-root RefList

-- The part of the native layer that the SMT-LIB value embedding is what
-- decides, and so cannot come out above this file, together with whatever of
-- the rest only this file reaches. See LeanMetaReduce::placeNativeDefs.
-- $native-place Smtm

/- Definition of SMT-LIB model semantics -/

noncomputable section

mutual

-- $native native_inhabited_type
def native_inhabited_type (T : SmtType) : native_Bool :=
  (native_and
    (native_not (native_Teq T SmtType.None))
    (native_Teq (__smtx_typeof_value (__smtx_type_default T)) T))
-- $native-end

$LEAN_SMT_EVAL_DEFS$

-- $native native_eval_fun_apply
def native_eval_fun_apply (M : SmtModel) (fid : native_String) (T U : SmtType) (i : SmtValue) : SmtValue :=
  let fallback := __smtx_type_default U
  if fid = native_default_fun_id then
    fallback
  else
    native_model_fun_lookup M fid T U i

-- $native native_unpack_seq
def native_unpack_seq : SmtSeq -> List SmtValue
  | (SmtSeq.cons v vs) => v :: (native_unpack_seq vs)
  | (SmtSeq.empty _) => []

-- $native native_pack_seq
def native_pack_seq (T : SmtType) : List SmtValue -> SmtSeq
  | [] => (SmtSeq.empty T)
  | v :: vs => (SmtSeq.cons v (native_pack_seq T vs))

-- $native native_ssm_char_of_value
def native_ssm_char_of_value : SmtValue -> native_Char
  | (SmtValue.Char c) => c
  | _ => 0

-- $native native_unpack_string
def native_unpack_string (x : SmtSeq) : native_String :=
  (native_unpack_seq x).map native_ssm_char_of_value

-- $native native_pack_string
def native_pack_string (s : native_String) : SmtSeq :=
  native_pack_seq SmtType.Char (s.map SmtValue.Char)

-- $native native_seq_len
def native_seq_len : List SmtValue -> native_Int
  | x => Int.ofNat x.length

-- $native native_seq_concat
def native_seq_concat : List SmtValue -> List SmtValue -> List SmtValue
  | x, y => x ++ y

-- $native native_seq_extract
def native_seq_extract (xs : List SmtValue) (i : native_Int) (n : native_Int) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || n <= 0 || i >= len then
    []
  else
    let start : Nat := Int.toNat i
    let take : Nat := Int.toNat (min n (len - i))
    (xs.drop start).take take

-- $native native_seq_indexof
/-- Generic sequence pattern operations share the regular expression matcher.
These small adapters also give the SMT backend distinct entry points that it
can map directly to the corresponding polymorphic `seq.*` operators. -/
def native_seq_indexof (xs pat : List SmtValue) (i : native_Int) : native_Int :=
  native_str_indexof_re xs (native_str_to_re pat) i

-- $native native_seq_contains
def native_seq_contains (xs pat : List SmtValue) : native_Bool :=
  0 <= native_seq_indexof xs pat 0

-- $native native_seq_replace
def native_seq_replace (xs pat repl : List SmtValue) : List SmtValue :=
  native_str_replace_re xs (native_str_to_re pat) repl

-- $native native_seq_replace_all
def native_seq_replace_all (xs pat repl : List SmtValue) : List SmtValue :=
  native_str_replace_re_all xs (native_str_to_re pat) repl

-- $native native_seq_occur_index
def native_seq_occur_index (xs pat : List SmtValue) (n : native_Int) : native_Int :=
  native_str_occur_index_re xs (native_str_to_re pat) n

-- $native native_seq_update
def native_seq_update (xs : List SmtValue) (i : native_Int) (ys : List SmtValue) : List SmtValue :=
  let len : native_Int := Int.ofNat xs.length
  if i < 0 || len <= i then
    xs
  else
    let idx := Int.toNat i
    (xs.take idx) ++ (ys.take (xs.length - idx)) ++
      (xs.drop (idx + ys.length))

-- $native native_seq_rev
def native_seq_rev : List SmtValue -> List SmtValue
  | xs => xs.reverse
-- $native-end

end

end

$LEAN_SMT_EVAL$

-- $native native_fun_typed
def native_fun_typed (M : SmtModel) : Prop :=
  ∀ fid A B i,
    __smtx_type_wf (SmtType.FunType A B) = true ->
    __smtx_typeof_value i = A ->
    __smtx_typeof_value (native_eval_fun_apply M fid A B i) = B ∧
      __smtx_value_canonical_bool (native_eval_fun_apply M fid A B i) = true
-- $native-end

def model_total_typed (M : SmtModel) : Prop :=
  (∀ isVar s T, __smtx_type_wf T = true ->
    __smtx_typeof_value (M.values { isVar := isVar, name := s, ty := T }) = T) ∧
  (∀ isVar s T, __smtx_type_wf T = true ->
    __smtx_value_canonical_bool
      (M.values { isVar := isVar, name := s, ty := T }) = true) ∧
  native_fun_typed M

/-
SMT interpretation is satisfiability, i.e. the existence of a model
interpreting the free constants.
-/
inductive smt_satisfiability : SmtTerm -> Bool -> Prop
  | intro_true  (t : SmtTerm) :
      (exists M : SmtModel, model_total_typed M /\ (__smtx_model_eval M t) = (SmtValue.Boolean true)) ->
      smt_satisfiability t true
  | intro_false (t : SmtTerm) :
      (forall M : SmtModel, model_total_typed M -> (__smtx_model_eval M t) = (SmtValue.Boolean false))->
      smt_satisfiability t false

/- ---------------------------------------------- -/

end Smtm
