# Parametric datatypes

The compiler supports uniform SMT-LIB parametric datatypes using the hooks in
[Logos's `parDt` parser](https://github.com/cvc5/logos/tree/parDt). The generic
parser rejects nested recursion, non-uniform recursion, and mutually recursive
blocks with different parameter arities.

Parameters are bound in the type term:

```lean
Term.DtParam : native_String → Term
Term.DatatypeParamType : native_String → Term → Term
```

`DatatypeParamType "X" T` binds `DtParam "X"` in `T`, which is a datatype type
or another parameter binder. For example, a two-parameter sort is represented by
`DatatypeParamType "X" (DatatypeParamType "Y" (DatatypeType "Pair" decl))`.
`DatatypeDecl` retains only its original `nil` and `cons` constructors; fields
of a template may contain free `DtParam` terms. The parser supplies canonical
parameter names `@p0`, `@p1`, and so on.

Sort instantiation is ordinary `Apply`. SMT translation normalizes the type
argument, substitutes it for one parameter in the binder's body, and continues
with that body. Substitution traverses plain datatype declarations and stops at
a binder for the same name. Embedded parameterized types thus keep their own
bindings. Partially applied types have no monomorphic SMT type.

Constructors and selectors carry **monomorphic declarations**, with no leading
type applications. The parser keeps generic operator information in its own
`ParserTerm` metadata, infers the required types from constructor arguments or
an operand's sort, and constructs `DtCons`/`DtSel` only after instantiation.
This also handles testers, updaters, and ascriptions such as
`(as nil (List Int))`. Unresolved generic operators become `Stuck` when they
leave the parser. Phantom parameters and nullary constructors need an
ascription when their arguments cannot be inferred.

The parser lowers sort annotations to monomorphic types before building
constants and variables. Types with identical instantiated declarations have
the same monomorphic representation, including unused phantom parameters.
The original CPC datatype helper programs can consequently operate on the
resulting constructors and selectors without a companion signature patch.

`__eo_to_smt_type : Term → SmtType` retains its one-argument interface. It
normalizes datatype type applications before calling the structural
`__eo_to_smt_type_mono` translator. SMT syntax remains monomorphic; constructor
and selector translation uses the ordinary monomorphic paths. There is no
translation scope or `__eo_to_smt_type_in`.

Normalization uses Lean's built-in `sizeOf` as its initial reduction budget.
Only instantiation consumes it; ordinary traversal decreases subtree size.
Ground arguments are normalized before substitution, so copying one introduces
no additional instantiation steps. Four lexicographic termination clauses
suffice, with no custom term-size function or handwritten theorem in `Spec.lean`.
The SMT backend computes a corresponding structural bound.

`Spec.lean` depends on `LogosTerm.lean` and the SMT model, never `Logos.lean`.
Changes to the specification are limited to parametric datatype translation;
the SMT model and quantifier semantics are unchanged.

## Integration test

With a built `ethos-eoc`, Lake, and a Logos checkout containing the `parDt` parser:

```sh
python3 tools/eoc/test/parametric_datatypes.py --logos ~/logos \
  --build-dir build-eoc --out-dir /tmp/eoc-parametric-test
```

The test regenerates CPC and checks parsing, typing, datatype rules, nested
parameters, malformed instances, and monomorphic SMT translation. It also
reports LOC using Logos's report script and checks that the specification has
no checker dependency. The Logos checkout is read only.
`--signature /path/to/Cpc.cached.eo` tests a separate signature copy;
`--no-generate` reuses the generated modules in the output directory.
