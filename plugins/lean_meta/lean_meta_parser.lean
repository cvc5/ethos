module

public import Logos.Parser.Datatypes
import all Logos.Parser.Datatypes
public import $EO_CALC$.Logos
import all $EO_CALC$.Logos

public section


namespace Eo

open SmtEval

private def parserNil (op : Term) : Option Term → Term
  | some seed => __eo_nil op (__eo_typeof seed)
  | none => __eo_nil op Term.Type

private def parserLiteral : Logos.Parser.Literal → Option Term
  | .numeral n => some (.Numeral n)
  | .rational num den => some (.Rational (native_mk_rational num den))
  | .string s => some (.String (native_string_lit s))
  | .binary width value => some (.Binary width value)

private def parserOps : List (Logos.Parser.OpDecl Term) := [
  { name := "Bool", arity := .exact 0, build := fun | [] => some .Bool | _ => none },
  { name := "false", arity := .exact 0,
    build := fun | [] => some (.Boolean false) | _ => none },
  { name := "true", arity := .exact 0,
    build := fun | [] => some (.Boolean true) | _ => none },
  { name := "->", arity := .rightAssoc,
    build := fun | [] => some .FunType | _ => none },
  { name := "@list", arity := .rightAssocNil (fun _ => .__eo_List_nil),
    build := fun | [] => some .__eo_List_cons | _ => none },
$LEAN_PARSER_OPS$]

/--
The macros introduced by a `define` with parameters in the Eunoia signature.
Eunoia inlines a definition, so it has no counterpart in the calculus itself; a
proof may nevertheless use it, which is why it is recorded here.  The body of
each is an application of the operator of `parserOps` generated for that
definition, indexed by the macro's parameters: indices are how an operator
declaration builds a term out of given arguments.  A `define` without
parameters needs no macro and is a nullary operator of `parserOps` instead.
-/
private def parserMacros : List (String × Logos.Parser.Macro) := [
$LEAN_PARSER_MACROS$]

/-- The proof rules of the calculus, by their name in the Eunoia signature. -/
private def parserRules : List (String × CRule) := [
$LEAN_PARSER_RULES$]

private def parserRuleMap : Std.HashMap String CRule := .ofList parserRules

private def parserRule (name : String) : Option CRule := parserRuleMap[name]?

private def parserConsView : DatatypeCons → List Term
  | .unit => []
  | .cons t c => t :: parserConsView c

private def parserDatatypeView : Datatype → List (List Term)
  | .null => []
  | .sum c d => parserConsView c :: parserDatatypeView d

private def parserDeclView : DatatypeDecl → Logos.Parser.DatatypeBlock Term native_String
  | .nil => []
  | .cons s d dd => (s, parserDatatypeView d) :: parserDeclView dd

private def parserConsBuild : List Term → DatatypeCons
  | [] => .unit
  | t :: c => .cons t (parserConsBuild c)

private def parserDatatypeBuild : List (List Term) → Datatype
  | [] => .null
  | c :: d => .sum (parserConsBuild c) (parserDatatypeBuild d)

private def parserDeclBuild : Logos.Parser.DatatypeBlock Term native_String → DatatypeDecl
  | [] => .nil
  | (s, d) :: dd => .cons s (parserDatatypeBuild d) (parserDeclBuild dd)

private def parserTermView : Term → Logos.Parser.DatatypeTermView Term native_String
  | .Apply f a => .apply f a
  | .DatatypeParamType p t => .param p t
  | .DatatypeTypeRef p => .ref p
  | .DatatypeType s dd => .datatype s (parserDeclView dd)
  | .DtcAppType t u => .constructorType t u
  | .DtCons s dd i => .constructor s (parserDeclView dd) i
  | .DtSel s dd i j => .selector s (parserDeclView dd) i j
$LEAN_PARSER_INDEXED_VIEW$
  | t => .atom t

private def parserTermBuild : Logos.Parser.DatatypeTermView Term native_String → Term
  | .apply f a => .Apply f a
  | .param p t => .DatatypeParamType p t
  | .ref p => .DatatypeTypeRef p
  | .datatype s dd => .DatatypeType s (parserDeclBuild dd)
  | .constructorType t u => .DtcAppType t u
  | .constructor s dd i => .DtCons s (parserDeclBuild dd) i
  | .selector s dd i j => .DtSel s (parserDeclBuild dd) i j
  | .indexed rebuild index => rebuild index
  | .atom t => t

private def parserDatatypeTerms : Logos.Parser.DatatypeTerms Term native_String where
  name := native_string_lit
  view := parserTermView
  build := parserTermBuild
  typeOf := __eo_typeof
  stuck := .Stuck

def parserConfig : Logos.Parser.Config Term CRule CCmd CCmdList where
  ops := parserOps
  parseLiteral := parserLiteral
  isType := (· == .Type)
  mkType := .Type
  mkUSort := .USort
  mkUConst := .UConst
  apply := .Apply
  parseRule := parserRule
  mkAssumePush := .assume_push
  mkStep := fun rule args premises =>
    .step rule (args.foldr .cons .nil)
      (premises.foldr (fun i rest => .cons (Int.ofNat i) rest) .nil)
  mkStepPop := fun rule args premises =>
    .step_pop rule (args.foldr .cons .nil)
      (premises.foldr (fun i rest => .cons (Int.ofNat i) rest) .nil)
  mkCheckProven := some .check_proven
  mkCmdList := (·.foldr .cons .nil)
$LEAN_PARSER_MK_VAR$


def parseProof (proof : String) : Except String (List Term × CCmdList) :=
  Logos.Parser.parseProofWithDatatypes parserDatatypeTerms parserConfig parserMacros proof

end Eo
