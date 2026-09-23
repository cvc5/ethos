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
private def template : DatatypeDecl :=
  .cons name (.sum .unit (.sum (.cons (.DtParam 0)
    (.cons (.DatatypeTypeRef name) .unit)) .null)) .nil
private def decl (t : Term) := DatatypeDecl.params (.cons t .nil) template
private def list (t : Term) := Term.DatatypeType name (decl t)
private def nil (t : Term) := Term.DtCons name (decl t) 0

-- Sort instances are single nodes, with distinct arguments even for phantom types.
#guard term (use lists "(L Int)") == some (list int)
#guard term (use lists "(L Bool)") == some (list .Bool)
#guard ty (use lists "(L Int)") == some .Type
#guard ty (use lists "(L Bool)") == some .Type
#guard ty (use lists "L") == some .Stuck
#guard ty (use lists "nil") == some .Stuck
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
#guard ty (use box "box") == some .Stuck
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
#guard __eo_subst_params (.cons int .nil) (.Apply (.UOp .Seq) (.DtParam 0)) ==
  .Apply (.UOp .Seq) int

-- An earlier datatype's arguments belong to this template; its fields do not.
private def nestedInstance := box ++
  " (declare-datatype Outer (par (X) ((outer (field (Box X))))))"
#guard hasType (use nestedInstance "(outer (as box (Box Int)))")
#guard __eo_subst_params (.cons int .nil)
    (.DatatypeType name (.params (.cons (.DtParam 0) .nil) template)) == list int

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
#guard __eo_typeof (.DtParam 0) == .Stuck
#guard __eo_typeof (.DatatypeType name (.params .nil template)) == .Stuck
#guard __eo_typeof (.DtCons name (.params (.cons (.Boolean true) .nil) template) 0) == .Stuck
#guard __eo_typeof (.DtSel name (.params (.cons (.DtParam 0) .nil) template) 1 0) == .Stuck
#guard __eo_typeof (.DatatypeType name template) == .Stuck

-- The instance's constructor list is what dt_split and dt-inst see.
private def x : Term := .UConst 0 (list int)
#guard __eo_typeof (__eo_prog_dt_split x) == .Bool
private def inst := use (lists ++ " (declare-const x (L Int))")
  "(= (is cons x) (= x (cons (head x) (tail x))))"
#guard (term inst).map __eo_prog_dt_inst == term inst

-- SMT declarations are monomorphic after translation; recursive references
-- remain relative to that declaration. These equalities are checked by Lean's kernel.
example : __eo_to_smt_type (list int) = .Datatype name
    (.cons name (.sum .unit (.sum (.cons .Int (.cons (.TypeRef name) .unit)) .null)) .nil) := by
  simp [list, decl, template, int, name, __eo_to_smt_type,
    __eo_to_smt_datatype, __eo_to_smt_datatype_cons,
    __eo_to_smt_datatype_decl_in, __eo_to_smt_type_in,
    __eo_to_smt_args, __eo_to_smt_param, __eo_to_smt_reserved_datatype_name,
    native_string_lit, native_string_prefix_eq, native_ite]
example : __eo_to_smt_type (.DtParam 0) = .None := by simp [__eo_to_smt_type, __eo_to_smt_type_in, __eo_to_smt_param]
example : __eo_to_smt_datatype_decl (decl int) =
    __eo_to_smt_datatype_decl_in (.cons .Int .unit) template := by
  simp [decl, int, __eo_to_smt_datatype_decl, __eo_to_smt_datatype_decl_in,
    __eo_to_smt_args, __eo_to_smt_type_in]
example : __eo_to_smt_type (list (list int)) = .Datatype name
    (.cons name (.sum .unit (.sum
      (.cons (__eo_to_smt_type (list int)) (.cons (.TypeRef name) .unit)) .null)) .nil) := by
  simp [list, decl, template, int, name, __eo_to_smt_type,
    __eo_to_smt_datatype, __eo_to_smt_datatype_cons,
    __eo_to_smt_datatype_decl_in, __eo_to_smt_type_in,
    __eo_to_smt_args, __eo_to_smt_param, __eo_to_smt_reserved_datatype_name,
    native_string_lit, native_string_prefix_eq, native_ite]

private def phantomTemplate : DatatypeDecl :=
  .cons (native_string_lit "Box") (.sum .unit .null) .nil
example : __eo_to_smt_datatype_decl (.params (.cons int .nil) phantomTemplate) =
    __eo_to_smt_datatype_decl (.params (.cons .Bool .nil) phantomTemplate) := by
  simp [phantomTemplate, __eo_to_smt_datatype_decl, __eo_to_smt_datatype_decl_in,
    __eo_to_smt_datatype, __eo_to_smt_datatype_cons]

-- The inner List binds its parameter to the outer second argument. Returning
-- to the next field restores the outer scope, including repeated parameters.
example : __eo_to_smt_datatype_cons (.cons .Int (.cons .Bool .unit))
    (.cons (list (.DtParam 1)) (.cons (.DtParam 0) (.cons (.DtParam 0) .unit))) =
    .cons (__eo_to_smt_type (list .Bool)) (.cons .Int (.cons .Int .unit)) := by
  simp [list, decl, template, name, __eo_to_smt_type, __eo_to_smt_type_in,
    __eo_to_smt_datatype_decl_in, __eo_to_smt_datatype, __eo_to_smt_datatype_cons,
    __eo_to_smt_args, __eo_to_smt_param, __eo_to_smt_reserved_datatype_name,
    native_string_lit, native_string_prefix_eq, native_ite]

-- An unwrapped declaration has its own empty scope, even when embedded in
-- a template. Ill-scoped parameters cannot capture the enclosing arguments.
example : __eo_to_smt_type_in (.cons .Int .unit) (.DatatypeType name template) =
    __eo_to_smt_type (.DatatypeType name template) := by
  simp [template, __eo_to_smt_type, __eo_to_smt_type_in]
example : __eo_to_smt_type_in (.cons .Int .unit) (.DtParam 1) = .None := by
  simp [__eo_to_smt_type_in, __eo_to_smt_param]

-- Generated sort cases preserve the parameter environment through Apply.
example : __eo_to_smt_type_in (.cons .Int (.cons .Bool .unit))
    (.Apply (.Apply (.UOp .Array) (.DtParam 0)) (.DtParam 1)) = .Map .Int .Bool := by
  simp [__eo_to_smt_type_in, __eo_to_smt_param,
    __smtx_typeof_guard, native_Teq, native_ite]

end ParametricDatatypesTest
