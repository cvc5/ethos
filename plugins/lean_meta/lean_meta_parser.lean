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

private def parserArgs (ts : List Term) : DatatypeArgs := ts.foldr .cons .nil

private def parserArgsList : DatatypeArgs → List Term
  | .nil => []
  | .cons t a => t :: parserArgsList a

private def parserGeneric (a : DatatypeArgs) : Bool :=
  let ts := parserArgsList a
  !ts.isEmpty && ts == (List.range ts.length).map Term.DtParam

private def parserAppSpine : Term → List Term → Term × List Term
  | .Apply f a, args => parserAppSpine f (a :: args)
  | f, args => (f, args)

-- Match ground argument types against a template. A parameter bound twice
-- must have the same type both times; another template's parameters are local.
mutual
private def parserMatchType (pat actual : Term) (bindings : Array (Option Term)) :
    Option (Array (Option Term)) :=
  match pat, actual with
  | .DtParam k, t => do
      let old ← bindings[k]?
      match old with
      | none => some (bindings.set! k (some t))
      | some u => if u == t then some bindings else none
  | .Apply f a, .Apply g b => do
      parserMatchType a b (← parserMatchType f g bindings)
  | .DatatypeType s (.params a dd), .DatatypeType t (.params b ee) =>
      if s == t && dd == ee then parserMatchArgs a b bindings else none
  | t, u => if t == u then some bindings else none

private def parserMatchArgs (a b : DatatypeArgs) (bindings : Array (Option Term)) :
    Option (Array (Option Term)) :=
  match a, b with
  | .nil, .nil => some bindings
  | .cons t a, .cons u b => do
      parserMatchArgs a b (← parserMatchType t u bindings)
  | _, _ => none
end

private def parserMatchFields (ty : Term) (args : List Term)
    (bindings : Array (Option Term)) : Option (Array (Option Term)) :=
  match args with
  | [] => some bindings
  | a :: args =>
      match ty with
      | .DtcAppType field rest => do
          parserMatchFields rest args (← parserMatchType field (__eo_typeof a) bindings)
      | _ => none

-- An operand supplies the instance for a selector, tester or updater.
private def parserInstanceArgs (s : native_String) (gen : DatatypeArgs)
    (dd : DatatypeDecl) (ty : Term) : Option DatatypeArgs :=
  match ty with
  | .DatatypeType t (.params a ee) =>
      if parserGeneric gen && s == t && dd == ee &&
          (parserArgsList gen).length == (parserArgsList a).length then some a else none
  | _ => none

private def parserInstantiate (op ty : Term) : Option Term :=
  match op with
  | .DtCons s (.params gen dd) i => do
      let a ← parserInstanceArgs s gen dd ty
      some (.DtCons s (.params a dd) i)
  | .DtSel s (.params gen dd) i j => do
      let a ← parserInstanceArgs s gen dd ty
      some (.DtSel s (.params a dd) i j)
  | _ => none

private def parserElaborate (term : Term) : Term := Id.run do
  let (head, args) := parserAppSpine term []
  let apply (head : Term) := args.foldl Term.Apply head
  match head with
  | .DatatypeType s (.params gen dd) =>
      if parserGeneric gen && args.length == (parserArgsList gen).length then
        return .DatatypeType s (.params (parserArgs args) dd)
  | .DtCons s (.params gen dd) i =>
      if parserGeneric gen then
        let ty := __eo_typeof_dt_cons_rec (.DatatypeType s (.params gen dd))
          (__eo_dd_resolve s (.params gen dd)) i
        if let some bindings := parserMatchFields ty args
            (Array.replicate (parserArgsList gen).length none) then
          if let some types := bindings.toList.mapM id then
            return apply (.DtCons s (.params (parserArgs types) dd) i)
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
  let decl := if arity == 0 then template else
    .params (parserArgs ((List.range arity).map Term.DtParam)) template
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
      mkParam := some Term.DtParam
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
