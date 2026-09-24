import Cpc.Parser
import Cpc.Spec

open Eo SmtEval Smtm

namespace ParametricDatatypesTest

private def term (input : String) : Option Term :=
  match Eo.parseProof input with
  | .ok ([t], _) => some t
  | _ => none

private def ty (input : String) : Option Term := (term input).map __eo_typeof
private def hasType (input : String) : Bool :=
  match ty input with | none | some .Stuck => false | some _ => true
private def use (prelude body : String) := prelude ++ " (assume p " ++ body ++ ")"

private def lists :=
  "(declare-datatype L (par (X) ((nil) (cons (head X) (tail (L X))))))"
private def int : Term := .UOp .Int
private def name := native_string_lit "L"
private def param := native_string_lit "@p0"
private def body : DatatypeDecl :=
  .cons name (.sum .unit (.sum (.cons (.DtParam param)
    (.cons (.DatatypeTypeRef name) .unit)) .null)) .nil
private def template := DatatypeDecl.param param body
private def list (t : Term) := Term.Apply (.DatatypeType name template) t
private def nil (t : Term) := Term.Apply (.DtCons name template 0) t

-- Sort instances retain ordinary applications, including phantom arguments.
#guard term (use lists "(L Int)") == some (list int)
#guard term (use lists "(L Bool)") == some (list .Bool)
#guard ty (use lists "(L Int)") == some .Type
#guard ty (use lists "(L Bool)") == some .Type
#guard ty (use lists "L") == some (.Apply (.Apply .FunType .Type) .Type)
#guard ty (use lists "nil") == some (.Apply (.Apply .FunType .Type) (list (.DtParam param)))
#guard ty (use lists "(L true)") == some .Stuck
#guard ty (use lists "(L Int Bool)") == some .Stuck
#guard term (use lists "(as nil (L Int))") == some (nil int)
#guard ty (use lists "(cons 1 (as nil (L Int)))") == some (list int)
#guard ty (use lists "(cons true (as nil (L Bool)))") == some (list .Bool)
#guard ty (use lists "(cons true (as nil (L Int)))") == some .Stuck
#guard ty (use lists "((as cons (L Int)) 1 (as nil (L Int)))") == some (list int)
#guard ty (use lists "(head (cons 1 (as nil (L Int))))") == some int
#guard ty (use lists "(tail (cons 1 (as nil (L Int))))") == some (list int)
#guard ty (use lists "((_ is cons) (cons 1 (as nil (L Int))))") == some .Bool
#guard ty (use lists "((_ update head) (cons 1 (as nil (L Int))) 2)") == some (list int)

#guard ty (use (lists ++ " (declare-sort U 0) (declare-const u U)")
  "(cons u (as nil (L U)))") == some (list (.USort 1))
#guard ty (use lists "(= (as nil (L Int)) (as nil (L Bool)))") == some .Stuck

private def box := "(declare-datatype Box (par (X) ((box))))"
#guard hasType (use box "box") -- a generic constructor still expects its type argument
#guard hasType (use box "(as box (Box Int))")
#guard term (use box "(Box Int)") != term (use box "(Box Bool)")

-- Two parameters, repeated occurrences, and parameters inside ordinary sorts.
private def pair := "(declare-datatype P (par (X Y) ((pair (first X) (second Y)))))"
#guard hasType (use pair "(pair 1 true)")
#guard ty (use pair "(pair 1 true)") == (ty (use pair "(as pair (P Int Bool))")).map
  (fun t => match t with | .DtcAppType _ (.DtcAppType _ r) => r | _ => .Stuck)
private def repeated := "(declare-datatype R (par (X) ((r (a X) (b X)))))"
#guard ty (use repeated "(r 1 true)") == some .Stuck
private def array := "(declare-datatype A (par (X Y) ((a (field (Array X Y))))))"
#guard ty (use (array ++ " (declare-const v (Array Int Bool))") "(field (a v))") ==
  some (.Apply (.Apply (.UOp .Array) int) .Bool)
-- A sequence field exercises substitution through Apply independently of parsing.
#guard __eo_subst_param param int (.Apply (.UOp .Seq) (.DtParam param)) ==
  .Apply (.UOp .Seq) int

-- An earlier datatype's arguments belong to this template; its fields do not.
private def nestedInstance := box ++
  " (declare-datatype Outer (par (X) ((outer (field (Box X))))))"
#guard hasType (use nestedInstance "(outer (as box (Box Int)))")
#guard __eo_subst_param param int (list (.DtParam param)) == list int
#guard __eo_subst_param param int (.DatatypeType name template) == .DatatypeType name template

-- Uniform mutual references retain the instance of their whole block.
private def mutuals :=
  "(declare-datatypes ((Tree 1) (Forest 1))
    ((par (X) ((leaf (value X)) (node (children (Forest X)))))
     (par (Y) ((empty) (more (tree (Tree Y)) (rest (Forest Y)))))))"
#guard ty (use mutuals "(value (leaf 1))") == some int
#guard ty (use mutuals "((_ is node) (node (more (leaf 1) (as empty (Forest Int)))))") == some .Bool

-- Parser restrictions: non-uniform, nested and mixed-arity blocks are refused.
#guard (term (use
  "(declare-datatype L (par (X) ((nil) (cons (tail (L Bool))))))" "true")).isNone
#guard (term (use (lists ++
  " (declare-datatype T ((leaf) (node (children (L T)))))") "true")).isNone
#guard (term (use
  "(declare-datatypes ((A 1) (B 0)) ((par (X) ((a))) ((b))))" "true")).isNone

-- Type checking rejects malformed hand-built instances independently of parsing.
#guard __eo_typeof (.DtParam param) == .Stuck
#guard __eo_typeof (list (.Boolean true)) == .Stuck
#guard __eo_typeof (list (.DtParam param)) == .Stuck
#guard __eo_typeof (.DatatypeType name body) == .Stuck
#guard __eo_typeof (.DatatypeType name (.param param template)) == .Stuck

-- The instance's constructor list is what dt_split and dt-inst see.
private def x : Term := .UConst 1 (list int)
#guard __eo_typeof (__eo_prog_dt_split x) == .Bool
private def inst := use (lists ++ " (declare-const x (L Int))")
  "(= (is cons x) (= x (cons (head x) (tail x))))"
#guard (term inst).map __eo_prog_dt_inst == term inst

-- Rules must see instantiated operators, and field positions exclude types.
private def split := use (lists ++ " (declare-const x (L Int))")
  "(or ((_ is nil) x) ((_ is cons) x))"
#guard some (__eo_prog_dt_split x) == term split
private def collapse := use lists "(= (head (cons 1 (as nil (L Int)))) 1)"
#guard (term collapse).map __eo_prog_dt_collapse_selector == term collapse
private def inject := use lists
  "(= (= (cons 1 (as nil (L Int))) (cons 2 (as nil (L Int))))
      (and (= 1 2) (= (as nil (L Int)) (as nil (L Int)))))"
#guard (term inject).map __eo_prog_dt_cons_eq == term inject

-- SMT declarations are monomorphic after instantiation. These closed
-- equalities are checked by Lean's kernel, with the one-argument entry point.
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def smtListDecl (t : SmtType) : SmtDatatypeDecl :=
  .cons name (.sum .unit (.sum (.cons t (.cons (.TypeRef name) .unit)) .null)) .nil
private def smtList (t : SmtType) : SmtType := .Datatype name (smtListDecl t)

attribute [local simp] __eo_to_smt_type __eo_to_smt_type_mono
  __eo_to_smt_dt_normalize.eq_def __eo_to_smt_dd_normalize.eq_def
  __eo_to_smt_dtd_normalize.eq_def __eo_to_smt_dtc_normalize.eq_def
  __eo_to_smt_dt_instantiate __eo_to_smt_dd_subst __eo_to_smt_dtd_subst
  __eo_to_smt_dtc_subst __eo_to_smt_dt_subst __eo_to_smt_datatype_decl
  __eo_to_smt_datatype __eo_to_smt_datatype_cons __eo_to_smt_reserved_datatype_name
  __eo_to_smt_dt_operator __eo_to_smt_dt_cons_type __eo_to_smt_dt_sel_type
  __eo_to_smt_apply __smtx_typeof_guard native_dt_budget
  native_ite native_teq native_Teq native_streq native_string_lit native_string_prefix_eq
  list nil int name param body template smtList smtListDecl

example : __eo_to_smt_type (list int) = smtList .Int := by simp
example : __eo_to_smt_type (list (list int)) = smtList (smtList .Int) := by simp
example : __eo_to_smt_type (list (list (list int))) = smtList (smtList (smtList .Int)) := by simp
example : __eo_to_smt_type (.DtParam param) = .None := by simp
example : __eo_to_smt_type (.DatatypeType name template) = .None := by simp

-- The same canonical name in two templates belongs to its own scope.
private def outerDecl := DatatypeDecl.param param
  (.cons (native_string_lit "Outer") (.sum (.cons (list (.DtParam param)) .unit) .null) .nil)
example : __eo_to_smt_type (.Apply (.DatatypeType (native_string_lit "Outer") outerDecl) int) =
    .Datatype (native_string_lit "Outer")
      (.cons (native_string_lit "Outer") (.sum (.cons (smtList .Int) .unit) .null) .nil) := by simp [outerDecl]

private def phantomDecl := DatatypeDecl.param param
  (.cons (native_string_lit "Box") (.sum .unit .null) .nil)
example : __eo_to_smt_type (.Apply (.DatatypeType (native_string_lit "Box") phantomDecl) int) =
    __eo_to_smt_type (.Apply (.DatatypeType (native_string_lit "Box") phantomDecl) .Bool) := by simp [phantomDecl]
example : __eo_to_smt_type (.Apply (.DatatypeType (native_string_lit "Box") phantomDecl) (.Boolean true)) =
    .None := by simp [phantomDecl]

private def pairName := native_string_lit "Pair"
private def param2 := native_string_lit "@p1"
private def pairDecl := DatatypeDecl.param param (.param param2
  (.cons pairName (.sum (.cons (.DtParam param)
    (.cons (.Apply (.Apply (.UOp .Array) (.DtParam param2)) (.DtParam param)) .unit)) .null) .nil))
attribute [local simp] pairName param2 pairDecl
example : __eo_to_smt_type (.Apply (.DatatypeType pairName pairDecl) int) = .None := by simp
example : __eo_to_smt_type (.Apply (.Apply (.DatatypeType pairName pairDecl) int) .Bool) =
    .Datatype pairName (.cons pairName
      (.sum (.cons .Int (.cons (.Map .Bool .Int) .unit)) .null) .nil) := by simp

example : __eo_to_smt (nil int) = .DtCons name (smtListDecl .Int) 0 := by
  simp [__eo_to_smt.eq_def]
example : __eo_to_smt (.Apply (.DtSel name template 1 0) int) =
    .DtSel name (smtListDecl .Int) 1 0 := by simp [__eo_to_smt.eq_def]
example : __eo_to_smt (.Apply (.Apply (.Apply (.DtCons name template 1) int) (.Numeral 1)) (nil int)) =
    .Apply (.Apply (.DtCons name (smtListDecl .Int) 1) (.Numeral 1))
      (.DtCons name (smtListDecl .Int) 0) := by
  simp [__eo_to_smt.eq_def, show sizeOf (1 : native_Int) = 2 from rfl]

end ParametricDatatypesTest
