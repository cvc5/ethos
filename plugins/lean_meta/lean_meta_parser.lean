module

public import Logos.Parser
import all Logos.Parser
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
  { name := "Type", arity := .exact 0, build := fun | [] => some .Type | _ => none },
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

/-- The argument types of one datatype constructor. -/
private def parserDatatypeCons (selectors : List (String × Term)) : DatatypeCons :=
  selectors.foldr (fun (_, ty) rest => .cons ty rest) .unit

/-- The constructors of one datatype, in declaration order. -/
private def parserDatatype (ctors : List (Logos.Parser.ConsSpec Term)) : Datatype :=
  ctors.foldr (fun c rest => .sum (parserDatatypeCons c.selectors) rest) .null

/-- The datatypes of one `declare-datatypes` block, in declaration order. -/
private def parserDatatypeDecl (dts : List (Logos.Parser.DatatypeSpec Term)) : DatatypeDecl :=
  dts.foldr (fun d rest => .cons (native_string_lit d.name) (parserDatatype d.constructors) rest) .nil

/--
The sort, constructor and selector bindings introduced by a `declare-datatypes`
block.  Constructors and selectors are identified by their position, so the
order here must match `parserDatatypeDecl`.
-/
private def parserDatatypeBindings (dts : List (Logos.Parser.DatatypeSpec Term)) :
    Option (List (String × Term)) :=
  let decl := parserDatatypeDecl dts
  some <| dts.flatMap fun d =>
    let name := native_string_lit d.name
    (d.name, Term.DatatypeType name decl) ::
      d.constructors.zipIdx.flatMap fun (c, i) =>
        (c.name, Term.DtCons name decl i) ::
          c.selectors.zipIdx.map fun ((sel, _), j) => (sel, Term.DtSel name decl i j)

def parserConfig : Logos.Parser.Config Term CRule CCmd CCmdList where
  ops := parserOps
  parseLiteral := parserLiteral
  isType := (· == .Type)
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
  mkCmdList := (·.foldr .cons .nil)
  datatypes := some
    { mkRef := fun name => Term.DatatypeTypeRef (native_string_lit name)
      mkDecls := parserDatatypeBindings }

/--
The initial state of the parser: the operators of the signature, together with
the identifiers its definitions introduce.
-/
private def parserState : Logos.Parser.State Term :=
  { Logos.Parser.State.ofOps parserOps with macros := .ofList parserMacros }

def parseProof (proof : String) : Except String (List Term × CCmdList) := do
  let ss ← Logos.Sexp.Parser.manySexps!.run proof
  (Logos.Parser.parseCommands parserConfig (Logos.Parser.unwrapProof ss)).run'
    parserState

end Eo
