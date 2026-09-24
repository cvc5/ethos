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

-- The generic parser supplies positions; use canonical names for their binders.
private def parserParamName (k : Nat) : native_String := native_string_lit ("@p" ++ toString k)

private def parserParams : DatatypeDecl → List native_String
  | .param s dd => s :: parserParams dd
  | _ => []

private def parserAppSpine : Term → List Term → Term × List Term
  | .Apply f a, args => parserAppSpine f (a :: args)
  | f, args => (f, args)

-- Match ground argument types against a template. A parameter bound twice
-- must have the same type both times; another template's parameters are local.
private def parserMatchType (names : List native_String) (pat actual : Term)
    (bindings : Array (Option Term)) : Option (Array (Option Term)) :=
  match pat, actual with
  | .DtParam s, t => do
      let (_, k) ← names.zipIdx.find? (fun (name, _) => name == s)
      let old ← bindings[k]?
      match old with
      | none => some (bindings.set! k (some t))
      | some u => if u == t then some bindings else none
  | .Apply f a, .Apply g b => do
      parserMatchType names a b (← parserMatchType names f g bindings)
  | t, u => if t == u then some bindings else none

private def parserMatchFields (names : List native_String) (ty : Term) (args : List Term)
    (bindings : Array (Option Term)) : Option (Array (Option Term)) :=
  match args with
  | [] => some bindings
  | a :: args =>
      match ty with
      | .DtcAppType field rest => do
          parserMatchFields names rest args (← parserMatchType names field (__eo_typeof a) bindings)
      | _ => none

-- An operand supplies the instance for a selector, tester or updater.
private def parserInstantiate (op ty : Term) : Option Term := do
  let (head, args) := parserAppSpine ty []
  match op, head with
  | .DtCons s dd _, .DatatypeType t ee
  | .DtSel s dd _ _, .DatatypeType t ee =>
      if s == t && dd == ee && args.length == (parserParams dd).length then
        some (args.foldl Term.Apply op)
      else none
  | _, _ => none

private def parserElaborate (term : Term) : Term := Id.run do
  let (head, args) := parserAppSpine term []
  let apply (head : Term) := args.foldl Term.Apply head
  -- Type applications, including an ascribed constructor's type arguments,
  -- are already explicit and stay as ordinary Apply nodes.
  if args.head?.any (fun a => __eo_typeof a == .Type) then
    return term
  match head with
  | .DtCons s dd i =>
      let names := parserParams dd
      if !names.isEmpty then
        let ty := __eo_typeof_dt_cons_rec
          (__eo_dt_generic_apply (.DatatypeType s dd) dd) (__eo_dd_resolve s dd) i
        if let some bindings := parserMatchFields names ty args
            (Array.replicate names.length none) then
          if let some types := bindings.toList.mapM id then
            return apply (types.foldl Term.Apply head)
  | .DtSel .. =>
      if let a :: _ := args then
        if let some op := parserInstantiate head (__eo_typeof a) then
          return apply op
$LEAN_PARSER_DATATYPE_INDEXED$
  | _ => pure ()
  return term

private def parserAscribe (op ty : Term) : Option Term :=
  match op with
  | .DtCons .. => parserInstantiate op ty
  | _ => none

/--
The sort, constructor and selector bindings introduced by a `declare-datatypes`
block.  Constructors and selectors are identified by their position, so the
order here must match `parserDatatypeDecl`.
-/
private def parserDatatypeBindings (dts : List (Logos.Parser.DatatypeSpec Term)) :
    Option (List (String × Term)) :=
  let template := parserDatatypeDecl dts
  let arity := (dts.head?.map (·.arity)).getD 0
  let decl := (List.range arity).foldr (fun k dd => .param (parserParamName k) dd) template
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
  mkType := .Type
  -- Tells apart the declarations of an overloaded name: a term the calculus
  -- gives no type to is not the reading meant.
  wellTyped := fun t => match __eo_typeof t with | .Stuck => false | _ => true
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
      mkDecls := parserDatatypeBindings
      mkParam := some fun k => Term.DtParam (parserParamName k)
      elaborate := parserElaborate
      ascribe := parserAscribe }
$LEAN_PARSER_MK_VAR$
/--
The initial state of the parser: the operators of the signature, together with
the identifiers its definitions introduce.
-/
private def parserState : Logos.Parser.State Term :=
  { Logos.Parser.State.ofOps parserOps with macros := .ofList parserMacros }

def parseProof (proof : String) : Except String (List Term × CCmdList) := do
  let ss ← Logos.Sexp.Parser.manySexps!.run proof
  (Logos.Parser.parseCommands parserConfig ss).run'
    parserState

end Eo
