# Parametric datatypes

The compiler implements phase one of the
[Logos `parDt` design](https://github.com/cvc5/logos/blob/parDt/docs/parametric-datatypes.md).
The generated Lean parser requires the `DatatypeOps.mkParam`, `elaborate` and
`ascribe` hooks from that branch. Uniform mutually recursive blocks are supported;
the generic Logos parser rejects nested recursion, non-uniform recursion and
blocks whose datatypes have different arities.

An instance is a single `Term.DatatypeType` node. Its `DatatypeDecl.params`
wrapper holds the arguments separately from a template whose fields use
`Term.DtParam` indices. Constructors and selectors carry the same wrapped
declaration. Monomorphic declarations retain their original representation.

The parser instantiates sorts, infers constructor arguments by matching ground
field types, instantiates selectors and indexed testers/updaters from their
operand, and handles constructor result-sort ascriptions such as
`(as nil (List Int))`. Parameters that cannot be inferred require an ascription,
including phantom parameters and nullary constructors. Elaboration proposes
instances; the generated typing checks reject generic declarations, non-type
arguments and out-of-range parameter indices.

The shared EO embedding implements substitution and the typing checks.
Substitution descends through applications and an embedded instance's arguments,
preserving the embedded template's own parameter scope. Declaration lookup skips
the wrapper, while resolution retains it on references to the same block.
Consequently `eo::dt_constructors`, `eo::dt_selectors`, `dt_split` and `dt-inst`
operate on the selected instance.

SMT translation carries an environment of already translated type arguments.
It translates an instance's arguments in the enclosing scope, then walks the
template with those arguments as its new environment. A `DtParam` becomes a
lookup. The translation therefore recurses structurally through the original
EO tree without building substituted declarations or translating an argument
again for each occurrence. The environment reuses `SmtDatatypeCons`, an existing
sequence of SMT types; the SMT model remains monomorphic and gains no parameter
constructors.

The public `eo_to_smt_type` and `eo_to_smt_datatype_decl` entry points start with
an empty environment. Generated type cases propagate the environment through
ordinary sort constructors such as `Array` and `Seq`. `Spec.lean` needs only
`LogosTerm.lean` and the SMT model: translation is total without custom size
measures, termination proofs or theorems in the specification. Existing
downstream proofs may need new datatype cases after regeneration; the compiler
does not update those handwritten proofs.

Run the integration test with a built `ethos-eoc`, Lake, and a Logos checkout
containing the `parDt` parser:

```sh
python3 tools/eoc/test/parametric_datatypes.py --logos ~/logos \
  --build-dir build-eoc --out-dir /tmp/eoc-parametric-test
```

It regenerates CPC using that checkout's cached signature and semantics, builds
the checker, parser and specification, and checks parsing, typing, datatype
rules, substitution scope, malformed instances and monomorphic SMT translation.
The Logos checkout is read only. `--no-generate` reuses the generated modules in
the output directory for repeated Lean checks.
