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

private def parserBinders : Term → List native_String × Term
  | .DatatypeParamType p t => let (ps, body) := parserBinders t; (p :: ps, body)
  | t => ([], t)

private def parserAppSpine : Term → List Term → Term × List Term
  | .Apply f a, args => parserAppSpine f (a :: args)
  | f, args => (f, args)

mutual
private def parserSubst (p : native_String) (a : Term) : Term → Term
  | .DtParam q => if p == q then a else .DtParam q
  | .DatatypeParamType q t =>
      if p == q then .DatatypeParamType q t else .DatatypeParamType q (parserSubst p a t)
  | .DatatypeType s dd => .DatatypeType s (parserSubstDecl p a dd)
  | .Apply t u => .Apply (parserSubst p a t) (parserSubst p a u)
  | .DtcAppType t u => .DtcAppType (parserSubst p a t) (parserSubst p a u)
  | t => t
private def parserSubstDecl (p : native_String) (a : Term) : DatatypeDecl → DatatypeDecl
  | .nil => .nil
  | .cons s d dd => .cons s (parserSubstDt p a d) (parserSubstDecl p a dd)
private def parserSubstDt (p : native_String) (a : Term) : Datatype → Datatype
  | .null => .null
  | .sum c d => .sum (parserSubstCons p a c) (parserSubstDt p a d)
private def parserSubstCons (p : native_String) (a : Term) : DatatypeCons → DatatypeCons
  | .unit => .unit
  | .cons t c => .cons (parserSubst p a t) (parserSubstCons p a c)
end

-- Matching a template can instantiate it with open parameters from another
-- declaration. Rename its formal parameters first to avoid capturing those
-- arguments. These temporary names are disjoint from parserParamName.
private def parserSubsts (names : List native_String) (args : List Term) (body : Term) : Term :=
  let fresh := names.zipIdx.map fun (_, i) => native_string_lit ("@inst" ++ toString i)
  let body := (names.zip fresh).foldl (fun t (p, q) => parserSubst p (.DtParam q) t) body
  (fresh.zip args).foldl (fun t (p, a) => parserSubst p a t) body

-- Elaboration is outside the trusted specification. Its output is checked by
-- __eo_typeof; constructors and selectors are built only after this lowering.
mutual
private partial def parserMono (t : Term) : Term :=
  match t with
  | .Apply f a =>
      let (head, args) := parserAppSpine t []
      let (names, body) := parserBinders head
      if !names.isEmpty && names.length == args.length then
        parserMono (parserSubsts names (args.map parserMono) body)
      else .Apply (parserMono f) (parserMono a)
  | .DatatypeType s dd => .DatatypeType s (parserMonoDecl dd)
  | .DtcAppType t u => .DtcAppType (parserMono t) (parserMono u)
  | t => t
private partial def parserMonoDecl : DatatypeDecl → DatatypeDecl
  | .nil => .nil
  | .cons s d dd => .cons s (parserMonoDt d) (parserMonoDecl dd)
private partial def parserMonoDt : Datatype → Datatype
  | .null => .null
  | .sum c d => .sum (parserMonoCons c) (parserMonoDt d)
private partial def parserMonoCons : DatatypeCons → DatatypeCons
  | .unit => .unit
  | .cons t c => .cons (parserMono t) (parserMonoCons c)
end

-- A generic operator is parser metadata, not a polymorphic EO constructor.
-- An unresolved generic is lowered to Stuck when it leaves the parser.
structure ParserTerm where
  value : Term
  generics : List (Term × Term) := [] -- prototype operator and its parameterized sort

private def parserResolved (t : ParserTerm) : Term :=
  if t.generics.isEmpty then t.value else .Stuck

private def parserLift (f : List Term → Term) (ts : List ParserTerm) : ParserTerm :=
  ⟨f (ts.map (·.value)), ts.flatMap (·.generics)⟩

mutual
private def parserMatchType (names : List native_String) (pat actual : Term)
    (bs : Array (Option Term)) : Option (Array (Option Term)) :=
  match pat, actual with
  | .DtParam p, t => do
      let (_, k) ← names.zipIdx.find? (fun (q, _) => p == q)
      let old ← bs[k]?
      match old with
      | none => some (bs.set! k (some t))
      | some u => if u == t then some bs else none
  | .Apply f a, .Apply g b | .DtcAppType f a, .DtcAppType g b => do
      parserMatchType names a b (← parserMatchType names f g bs)
  | .DatatypeType s dd, .DatatypeType t ee =>
      if s == t then parserMatchDecl names dd ee bs else none
  | t, u => if t == u then some bs else none
private def parserMatchDecl (names : List native_String) (dd ee : DatatypeDecl)
    (bs : Array (Option Term)) : Option (Array (Option Term)) := do
  match dd, ee with
  | .nil, .nil => some bs
  | .cons s d dd, .cons t e ee =>
      if s == t then parserMatchDecl names dd ee (← parserMatchDt names d e bs) else none
  | _, _ => none
private def parserMatchDt (names : List native_String) (d e : Datatype)
    (bs : Array (Option Term)) : Option (Array (Option Term)) := do
  match d, e with
  | .null, .null => some bs
  | .sum c d, .sum b e => parserMatchDt names d e (← parserMatchCons names c b bs)
  | _, _ => none
private def parserMatchCons (names : List native_String) (c d : DatatypeCons)
    (bs : Array (Option Term)) : Option (Array (Option Term)) := do
  match c, d with
  | .unit, .unit => some bs
  | .cons t c, .cons u d => parserMatchCons names c d (← parserMatchType names t u bs)
  | _, _ => none
end

private def parserMatchFields (names : List native_String) (ty : Term) (args : List Term)
    (bs : Array (Option Term)) : Option (Array (Option Term)) :=
  match args, ty with
  | [], _ => some bs
  | a :: args, .DtcAppType field rest => do
      parserMatchFields names rest args (← parserMatchType names field (__eo_typeof a) bs)
  | _, _ => none

private def parserInstantiate (generics : List (Term × Term)) (op ty : Term) : Option Term := do
  let (_, generic) ← generics.find? (fun (g, _) => g == op)
  let (names, body) := parserBinders generic
  let actual := parserMono ty
  let _ ← parserMatchType names (parserMono body) actual (Array.replicate names.length none)
  match op, actual with
  | .DtCons s _ i, .DatatypeType t dd => if s == t then some (.DtCons s dd i) else none
  | .DtSel s _ i j, .DatatypeType t dd => if s == t then some (.DtSel s dd i j) else none
  | _, _ => none

private def parserElaborate (term : ParserTerm) : ParserTerm := Id.run do
  let (head, args) := parserAppSpine term.value []
  let finish (inst old : Term) : ParserTerm :=
    ⟨args.foldl Term.Apply inst, term.generics.filter (fun (g, _) => g != old)⟩
  match head with
  | .DtCons s dd i =>
      if let some (_, generic) := term.generics.find? (fun (g, _) => g == head) then
        let (names, _) := parserBinders generic
        let ty := parserMono (__eo_typeof_dt_cons_rec (.DatatypeType s dd) (__eo_dd_resolve s dd) i)
        if let some bs := parserMatchFields names ty args (Array.replicate names.length none) then
          if let some types := bs.toList.mapM id then
            if let some inst := parserInstantiate term.generics head (types.foldl Term.Apply generic) then
              return finish inst head
  | .DtSel .. =>
      if let a :: _ := args then
        if let some inst := parserInstantiate term.generics head (__eo_typeof a) then
          return finish inst head
$LEAN_PARSER_DATATYPE_INDEXED$
  | _ => pure ()
  return term

private def parserAscribe (op ty : ParserTerm) : Option ParserTerm := do
  if __eo_typeof (parserResolved ty) != .Type then none else do
    match op.value with
    | .DtCons .. =>
        if op.generics.isEmpty then
          if __eo_typeof op.value == parserMono ty.value then some op else none
        else do
          let inst ← parserInstantiate op.generics op.value ty.value
          some ⟨inst, []⟩
    | _ => none

private def parserDatatypeBindings (dts : List (Logos.Parser.DatatypeSpec ParserTerm)) :
    Option (List (String × ParserTerm)) :=
  let raw : List (Logos.Parser.DatatypeSpec Term) := dts.map fun d =>
    { name := d.name, arity := d.arity, constructors := d.constructors.map fun c =>
      { name := c.name, selectors := c.selectors.map fun (s, t) => (s, parserResolved t) } }
  let template := parserDatatypeDecl raw
  let arity := (dts.head?.map (·.arity)).getD 0
  let template := if arity == 0 then parserMonoDecl template else template
  some <| dts.flatMap fun d =>
    let name := native_string_lit d.name
    let sort := (List.range arity).foldr (fun k t => .DatatypeParamType (parserParamName k) t)
      (.DatatypeType name template)
    let generic (op : Term) : ParserTerm := ⟨op, if arity == 0 then [] else [(op, sort)]⟩
    (d.name, ⟨sort, []⟩) :: d.constructors.zipIdx.flatMap fun (c, i) =>
      (c.name, generic (.DtCons name template i)) ::
        c.selectors.zipIdx.map fun ((sel, _), j) => (sel, generic (.DtSel name template i j))

private def parserArity : Logos.Parser.Arity Term → Logos.Parser.Arity ParserTerm
  | .exact n => .exact n
  | .leftAssoc => .leftAssoc
  | .rightAssoc => .rightAssoc
  | .rightAssocNil nil => .rightAssocNil fun t => ⟨nil (t.map (·.value)), t.toList.flatMap (·.generics)⟩
  | .chainable f => .chainable (parserLift f)
  | .argList f => .argList (parserLift f)

private def parserLiftOp (op : Logos.Parser.OpDecl Term) : Logos.Parser.OpDecl ParserTerm :=
  { name := op.name, indexArity := op.indexArity, arity := parserArity op.arity,
    build := fun ts => (op.build (ts.map (parserMono ∘ (·.value)))).map fun t =>
      ⟨t, ts.flatMap (·.generics)⟩,
    binder := op.binder.map parserLift }

private def parserBaseConfig : Logos.Parser.Config Term CRule CCmd CCmdList where
  ops := parserOps
  parseLiteral := parserLiteral
  isType := (· == .Type)
  mkType := .Type
  mkUSort := .USort
  mkUConst := .UConst
  apply := .Apply
  parseRule := parserRule
  mkAssumePush := .assume_push
  mkStep := fun rule args premises => .step rule (args.foldr .cons .nil)
    (premises.foldr (fun i rest => .cons (Int.ofNat i) rest) .nil)
  mkStepPop := fun rule args premises => .step_pop rule (args.foldr .cons .nil)
    (premises.foldr (fun i rest => .cons (Int.ofNat i) rest) .nil)
  mkCmdList := (·.foldr .cons .nil)
$LEAN_PARSER_MK_VAR$

def parserConfig : Logos.Parser.Config ParserTerm CRule CCmd CCmdList where
  ops := parserOps.map parserLiftOp
  parseLiteral := fun l => (parserLiteral l).map (fun t => ⟨t, []⟩)
  isType := fun t => parserResolved t == .Type
  mkType := ⟨.Type, []⟩
  wellTyped := fun t => __eo_typeof (parserResolved t) != .Stuck
  mkUSort := fun i => ⟨.USort i, []⟩
  mkUConst := fun i t => ⟨.UConst i (if __eo_typeof (parserResolved t) == .Type then parserMono t.value else .Stuck), []⟩
  apply := fun f a => ⟨.Apply f.value a.value, f.generics ++ a.generics⟩
  parseRule := parserRule
  mkAssumePush := parserBaseConfig.mkAssumePush ∘ parserResolved
  mkStep := fun r ts ps => parserBaseConfig.mkStep r (ts.map parserResolved) ps
  mkStepPop := fun r ts ps => parserBaseConfig.mkStepPop r (ts.map parserResolved) ps
  mkCmdList := parserBaseConfig.mkCmdList
  mkVar := parserBaseConfig.mkVar.map fun mk s t => ⟨mk s (parserMono (parserResolved t)), []⟩
  datatypes := some
    { mkRef := fun s => ⟨.DatatypeTypeRef (native_string_lit s), []⟩
      mkDecls := parserDatatypeBindings
      mkParam := some fun k => ⟨.DtParam (parserParamName k), []⟩
      elaborate := parserElaborate
      ascribe := parserAscribe }

private def parserState : Logos.Parser.State ParserTerm :=
  { Logos.Parser.State.ofOps parserConfig.ops with macros := .ofList parserMacros }

def parseProof (proof : String) : Except String (List Term × CCmdList) := do
  let ss ← Logos.Sexp.Parser.manySexps!.run proof
  let (ts, cmds) ← (Logos.Parser.parseCommands parserConfig ss).run' parserState
  return (ts.map parserResolved, cmds)

end Eo
