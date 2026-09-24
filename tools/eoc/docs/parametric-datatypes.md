# Parametric datatypes

The compiler supports uniform SMT-LIB parametric datatypes using the hooks in
[Logos's `parDt` parser](https://github.com/cvc5/logos/tree/parDt). The generic
parser rejects nested recursion, non-uniform recursion, and mutually recursive
blocks with different parameter arities.

A declaration binds one named parameter at a time:

```lean
Term.DtParam : native_String → Term
DatatypeDecl.param : native_String → DatatypeDecl → DatatypeDecl
```

`param "X" dd` binds `DtParam "X"` in the template. Multiple parameters are
nested binders. The current Logos parser supplies parameter positions, which
the generated adapter gives canonical names `@p0`, `@p1`, and so on. Each
embedded datatype declaration introduces its own scope.

Instances remain ordinary applications. For example, `List Int` is
`Apply (DatatypeType "List" listDecl) Int`, and a constructor at that sort is
`Apply (DtCons "List" listDecl i) Int`. This preserves phantom arguments and
keeps monomorphic declarations unchanged. There is no argument-wrapper
constructor or additional argument datatype.

Generic sorts and constructors expect one type argument per binder. Applying a
constructor or selector to a type substitutes that one named parameter in its
result type. The checker rejects undeclared or duplicate parameter names and
non-type arguments. Recursive references resolve to the enclosing block applied
to its formal parameters; substitution then supplies the actual arguments.

The parser infers omitted constructor type arguments from ground field types.
It supplies selector, tester, and updater type arguments from their operand's
sort, and handles constructor result-sort ascriptions such as
`(as nil (List Int))`. Nullary constructors and phantom parameters need an
ascription when their arguments cannot be inferred.

SMT translation first normalizes EO datatype applications. Each application
normalizes its argument, removes one `DatatypeDecl.param` binder, and substitutes
that argument into the remaining declaration. Substitution leaves embedded
datatype declarations alone: their parameters belong to those declarations.
It still traverses their external arguments, so `Outer X` containing `List X`
instantiates correctly even when both templates use the same parameter name.

`__eo_to_smt_type : Term → SmtType` keeps its one-argument interface. It passes
the normalized type to `__eo_to_smt_type_mono`, the ordinary structural
translator. There is no translation scope or `__eo_to_smt_type_in`. SMT syntax
stays monomorphic, and a partially applied template has no ground SMT type.
Constructors and selectors use the same normalization before translation.

Normalization uses Lean's built-in `sizeOf` as an initial reduction budget.
Only instantiation consumes it; traversal decreases the input subtree size.
Ground arguments are normalized before substitution, so copying them introduces
no further instantiation steps. Four lexicographic termination clauses suffice;
there is no custom term-size function or handwritten theorem in `Spec.lean`.
The SMT backend computes a corresponding structural bound.

`Spec.lean` imports only `LogosTerm.lean` and the SMT model, with no dependency
on `Logos.lean`. Changes to the specification are limited to parametric datatype
translation; the existing SMT model and quantifier semantics are unchanged.

## CPC helper compatibility

CPC's original helper programs assume that constructor identities have no
explicit type applications. The companion
[Logos patch](logos-apply-datatypes.patch) updates the cached CPC signature to:

- Return instantiated constructors for an applied datatype sort.
- Resolve either a generic or an instantiated constructor to its instance.
- Instantiate selectors using their operand's sort.
- Exclude type arguments from constructor fields and injectivity equations.

The equivalent changes should also be made in the upstream CPC source before
regenerating the cached signature. To apply the patch to a Logos checkout:

```sh
git -C ~/logos apply /path/to/ethos/tools/eoc/docs/logos-apply-datatypes.patch
```

## Integration test

With a built `ethos-eoc`, Lake, and a Logos checkout containing the `parDt`
parser and the updated CPC signature:

```sh
python3 tools/eoc/test/parametric_datatypes.py --logos ~/logos \
  --build-dir build-eoc --out-dir /tmp/eoc-parametric-test
```

The test regenerates CPC, builds its checker, parser, and specification, and
checks parsing, typing, datatype rules, named parameters, malformed instances,
and monomorphic SMT translation. It also reports LOC using Logos's report script
and checks that the specification has no checker dependency.
The Logos checkout is read only.
`--signature /path/to/Cpc.cached.eo` tests a separate signature copy;
`--no-generate` reuses the generated modules in the output directory.
