# The cvc5 proof pipeline

This document summarizes how a cvc5 proof is produced, checked, and verified.
It covers one pipeline. The compiler described here is experimental; a
successful generation run does not establish the soundness of the calculus:

```
input.smt2 -> cvc5 parser -> cvc5 API -> cvc5 internals -> proof.cpc
                                                              |
                                                Cpc.eo -> ethos -> accept/reject
                                                   |
                                                   +-> desugar -> model-smt -+-> rule.smt2
                                                                      ^      +-> Logos (Lean)
                                                                      |
                                                        *.eos -> sem_compile.py
```

Stages 1 to 3 produce a proof in the CPC calculus. Stage 4 checks that proof
against the CPC signature, `Cpc.eo`. Stages 5 to 7 compile `Cpc.eo` itself
into a verification condition or a Lean theorem, which supplies obligations for
establishing that the rules the checker applies are sound. Those obligations
still need to be discharged against the chosen model. Stages 1 to 4 run on every
query; stages 5 to 7 run offline, per proof rule.

Three code bases are involved. Only ethos is this repository:

| Code base | Role |
| --- | --- |
| cvc5 | solves the query and prints a CPC proof |
| ethos (this repository) | checks proofs against a supplied Eunoia signature; the experimental compiler translates that signature |
| Logos | the Lean development in which the checker is proved correct |

CPC is defined in cvc5, not in Ethos. For the current proof-production
interface, consult the cvc5 checkout that supplies the signature.

Stages 5 to 7 are the `ethos-eoc` binary, built from the standalone project in
[`plugins/`](../../../plugins) and driven by
[`tools/eoc/driver.py`](../driver.py):

```bash
cmake -S plugins -B build-eoc
cmake --build build-eoc --target ethos-eoc -j8

# a verification condition for one rule
python3 tools/eoc/driver.py vc --build-dir build-eoc \
  --semantics tools/eoc/semantics/development-cpc.eos \
  <input.eo> <proof-rule>

# the whole CPC signature, compiled to Lean
python3 tools/eoc/driver.py lean --build-dir build-eoc --all \
  --semantics tools/eoc/semantics/development-cpc.eos \
  <cvc5>/proofs/eo/cpc/Cpc.eo
```

`--semantics` names what the *input's* symbols mean to a model and
`--smt-semantics` the SMT-LIB semantics they are written against; both name a
configuration the driver compiles before any stage runs, see stage 6.

See [`tools/eoc/README.md`](../README.md) for the full driver
interface.

## Stages 1 to 3: proof production

cvc5 parses an SMT-LIB problem, solves it and emits a CPC proof. The signature
must match the vocabulary and rules used by the proof. These stages are owned
by cvc5 and are outside this compiler's checks. The compiler takes the
signature as input; it does not build or invoke a solver to produce the proof.

## Stage 4: the ethos parser and checker

The parser applies the operator properties declared in the signature —
`:right-assoc-nil`, `:right-assoc`, `:left-assoc-nil`, `:left-assoc`,
`:right-assoc-non-singleton-nil`, `:left-assoc-non-singleton-nil`,
`:chainable`, `:pairwise`, `:arg-list`, `:binder` and `:let-binder` — and
lowers n-ary literal operations to binary ones, so that `(eo::add a b c)`
becomes `(eo::add (eo::add a b) c)`.

Ethos then checks the proof against the supplied signature. Its `correct`
response relies on the checker, GMP and the rules in that signature; it does
not establish that the rules are sound. The remaining stages supply
obligations about the signature and its interpretation. See the
[Ethos responses](../../../user_manual.md#responses).

## The deep embedding

Stages 5 to 7 share one target. A datatype `eo.Term` is declared with builtin
constructors such as `eo.Stuck` and `eo.Apply`, and every constant in the
Eunoia signature becomes a constructor of that datatype.

Under the SMT backend, Eunoia programs become uninterpreted functions and
their definitions become quantified axioms; a program that is forward declared
but never defined stays a free uninterpreted function. Under the Lean backend,
Eunoia programs become Lean definitions.

A rule's soundness is then a question about the syntactic space of Eunoia
terms: is there a term witnessing that the rule is unsound? `unsat` from the
SMT backend means there is no such term in the generated encoding. The
conclusion depends on the correctness and consistency of that encoding and
the supplied semantics.

Terms carry a *meta-kind* saying what their embedding is: a Eunoia term, an SMT
term, an SMT type, an SMT value, a map or sequence value, a builtin, a proof,
a checker rule or command. Types applied to `$native_embed_eo`,
`$native_embed_smt` or `$native_embed_checker` in the Eunoia templates declare
which of the three layers a datatype belongs to. See `MetaKind` in
[`plugins/utils.h`](../../../plugins/utils.h).

## Stage 5: desugar

Compiles `*.eo` to `*.eo`, rewriting non-essential Eunoia features into Eunoia
programs. It emits a forward declaration of the side condition `$eo_model_sat`,
which stage 6 defines.

Optionally a proof rule is compiled to a Eunoia program `$eo_prog_X` that
operates over *formulas* rather than proofs, plus a program `$eovc_X` that
calls `$eo_model_sat` and `$eo_prog_X` and evaluates successfully exactly when
the rule is unsound. `$eovc_X` is what stage 7a verifies.

The pass is `plugins/desugar/`: `desugar.{h,cpp}`, the `eo_desugar.eo`
template, `native_embed.eo` (what the natives are written over -- the `$native_apply_*`
and `$native_type_*` constructors, the type aliases, and the definitions
written over other natives; the natives themselves are compiled into it from
`plugins/desugar/natives.eos`, one line to a native), and
`eo_desugar_native.eo` (the SMT-like builtins of Eunoia, and the declarations
of the *Eunoia* deep embedding, `eo.Term` and the `$emb_X` constructor of each
symbol). Two parts are optional: `plugins/trim_defs/`, which slices the
signature down so the resulting VCs stay manageable, and
`desugar_checker.{h,cpp}` with `eo_desugar_checker.eo`, which desugars the
executable checker.

What the pass rewrites:

- `define` commands are inlined. Each definition is re-emitted as
  `$parse_<name>`, which only stage 7b consumes, to build the generated proof
  parser's tables. Definitions whose own name starts with `$` are signature
  helpers and are not preserved.
- Optionally, evaluation is flattened: evaluation nested inside ordinary
  applications is lifted, so that stuckness propagates eagerly through ordinary
  constant applications, and each `eo::requires` and `eo::ite` becomes a
  program.
- For `declare-rule`, the proof type is handled as part of generating
  `$eovc_X`.
- For `declare-consts`, `$eo_lit_type_Numeral`, `$eo_lit_type_Rational`,
  `$eo_lit_type_String` and `$eo_lit_type_Binary` become references to builtin
  types.
- Operator overloading is resolved through the `$eoo_X.N` naming convention.
- Ambiguously typed functions become unambiguous functions taking an opaque
  type argument, with a helper program invoked on that type, so that
  `(as nil (List Int))` becomes the opaque application `(nil (List Int))`.
- `eo::cons` is desugared, as is the `eo::list_*` family (`list_len`,
  `list_concat`, `list_nth`, `list_find`, `list_rev`, `list_erase`,
  `list_erase_all`, `list_setof`, `list_minclude`, `list_meq`) and `eo::nil`,
  the last with a case auto-generated for each `:right-assoc-nil` and
  `:left-assoc-nil` operator. The user-defined cases of `eo::dt_constructors`,
  `eo::dt_selectors` and `eo::typeof` are desugared too.
- `eo::typeof` *approximates* Eunoia's internal type system by monomorphizing
  partial applications: there is a type rule for `(= x)`, not for `=`. A case
  is auto-generated for every user symbol, into `$eo_typeof_main`.
- `declare-datatype` and `declare-datatypes` are eliminated into ordinary types
  and constants. Datatype, constructor and selector semantics survive as the
  auto-generated `eo::dt_constructors` and `eo::dt_selectors` cases.

## Stage 6: model-smt

Compiles `*.eo` to `*.eo`, adding the definition of `$eo_model_sat`: SMT-LIB
model semantics, written in Eunoia.

None of that semantics is hardcoded in C++. It is stated by two signatures
written directly in the deep embedding, both read by this stage alone:

| File | What it says |
| --- | --- |
| `tools/eoc/out/smt_defs.eo` | the SMT-LIB signature, which is the target and so is fixed |
| `tools/eoc/out/user_defs.eo` | how the symbols of the input transform into it |

Each is a sequence of blocks, one per symbol, opened by a `; -- X` line. For a
symbol `X`, `smt_defs.eo` gives the embedding constructor `$emb_sm.X` and the
macro `$sm_X`, the cases `X` contributes to `$smtx_typeof` and to the
evaluation program `$smtx_model_eval` (as `$eoc_typeof_X` and `$eoc_eval_X`),
and the auxiliary programs those cases call. `user_defs.eo` gives
`$eoc_transform_X`, the cases `X` contributes to `$eo_to_smt`, and
`$eoc_transform_type_X` for a type constructor.

**Both files are generated.** What is written by hand is a *configuration*
under [`tools/eoc/semantics/`](../semantics), which
`tools/eoc/compiler/sem_compile.py` compiles into them; the driver runs it
before any stage, so the two are never out of step with what the stage reads.

| Configuration | Compiles to |
| --- | --- |
| `semantics/smt.eos`, named by `--smt-semantics` | `smt_defs.eo`, `smt_termination.lean` |
| `semantics/development-cpc.eos`, named by `--semantics` | `user_defs.eo`, `user_termination.lean` |
| `plugins/desugar/desugar.eos` | `user_desugar.eo`, the input's nil predicates |
| `plugins/desugar/natives.eos` | `native_defs.eo`, the natives the embedding calls |
| `plugins/model_smt/model_smt.eos` | the head of each signature above, which says how the stage takes it apart |
| `plugins/lean_meta/lean.eos` | `lean_native.lean`, the native layer of stage 7b |
| `plugins/smt_meta/smt-vc.eos` | `smt_vc_native.smt2`, the native layer of stage 7a |

The first two a run may name another of; the rest are fixed, since they say
what the embedding is rather than what a signature means.

`smt.eos` is the target, so every input is compiled through it and nothing
about an input is asked of it. `development-cpc.eos` is a *test*, kept so that
the compiler and the stages after it have a real signature to run over; **as of 2026-09-18, Logos supplies its CPC semantics in `install/defs/Cpc.eos`**, and that is what a
run meaning to say something about CPC names with `--semantics`. A set from another tree still compiles into the fixed role-specific files
under `tools/eoc/out/`; the source set itself is not modified.

A configuration says what each symbol means once, in the vocabulary of SMT-LIB
and of the input, and the compiler works out the programs, the constructors and
the cases it compiles to:

```lisp
(define-symbol select (a i)
  :typeof ($smtx_typeof_select a i)
  :eval (a i) ($smtx_map_select a i))
```

`a` and `i` stand for the *values* its arguments evaluate to under `:eval` and
for their *types* under `:typeof`, the level being read off the place each
stands in, so neither is said twice.

Its forms are `define-symbol`, `define-sort`, `declare-constructor`,
`define-literal`, `define-method`, `define-rule`, `program`, `define-macro` and
`section`, and **nothing else**: a form the compiler cannot read is refused rather than copied
into the generated file, so everything a signature names has been checked
against the vocabulary of the embedding, ordered against the other blocks, and
can be trimmed with them. A set therefore says what a theory *does* and never
what the embedding *is*. `tools/eoc/docs/semantics.md` is the reference for
the language.

`defs_reader.{h,cpp}` reads a generated file as *text* blocks and splices the
cases into the aggregate programs, copying everything else through unchanged.
Reading text rather than terms is what stops the embedding definitions from
being expanded on the way. The plugin algorithms hold no per-symbol semantics:
they take the blocks the input needs together with the blocks those name, put
what each says where it belongs in the template, and check that no declared
symbol was left without a meaning. Where each form goes is settled by the name
it defines -- a constructor with the terms, the types or the values of its
family, and every auxiliary program together in one stream before the first
aggregate whose cases may call one. Which aggregates there are the stage does
not know: the head of each generated file declares them, one line to an
aggregate, saying what a symbol's case is named and the marker of the template
its cases are written at. Those lines are compiled from
`plugins/model_smt/model_smt.eos`, so an aggregate is added there and in
`tools/eoc/compiler/sem_target.py`, and this stage needs no change and no
rebuild.

A block may also say that the compilation has no place for its symbol. The
configuration writes `:exclude` on the symbol, the method or the rule; the
compiler turns that into an `eoc-exclude` directive, and the desugar stage
drops what it names.

What stays in `plugins/model_smt/model_smt.eo` is the embedding itself: the
term, type and value languages it declares -- including the shapes a value is
built over, the map an array and a set are and the sequence a string is -- the
binders, the application, the datatypes an input declares, the programs over
types that everything else is written against, and the default case of each
aggregate. Which symbols and theories there are it does not say; that is the
configuration's, down to the literals and to `ite` and `=`, which are written
there as ordinary symbols that say `:keep` so a signature trimmed to a handful
of rules still has them.

This stage also reduces the Eunoia builtins to SMT-LIB literal semantics:
`eo::eq`; `eo::not`, `eo::and`, `eo::or`, `eo::xor`; `eo::add`, `eo::mul`,
`eo::qdiv`, `eo::zdiv`, `eo::zmod`, `eo::is_neg`, `eo::neg`; `eo::len`,
`eo::concat`, `eo::extract`, `eo::find`; `eo::to_z`, `eo::to_q`, `eo::to_bin`,
`eo::to_str`; and `eo::var`, `eo::nameof`, which represent variables as the
constant `$eot_Var`. The macros definable in terms of those — `eo::is_eq`,
`eo::is_z`, `eo::is_q`, `eo::is_bin`, `eo::is_str`, `eo::is_bool`,
`eo::is_var`, `eo::gt` and `eo::cmp` — are done here rather than in stage 5,
so that desugaring never forward-references `eo::`.

Two more things are completed here. `eo::typeof` gains the literal types and
the type of variables (`$eot_Var`), referring back to `$eo_typeof_main`. And
`eo::is_ok` is defined in terms of the deep embedding: `$eo_is_ok` asks whether
the term under test embeds as `eo.Stuck`.

The SMT-LIB semantics proper consist of the core evaluation semantics
`$smtx_model_eval`; `$smtx_type_default`, which returns the first term of a
finite type, beside `$smtx_type_wf` and `$smtx_type_bounded`, which say whether
the values of a type are a set at all and whether they are finitely many; and,
written in the configuration beside the sorts they belong to, the programs over
a map value -- lookup, canonical update, the type of one and whether it is
written the one way -- and their counterparts over a sequence value.

A map value is what an array and a set are. A *function* value is not one:
`$vsm_Fun` carries only a name and the two halves of its type, and applying one
is left to the model, so `$smtx_model_eval_apply` hands it to the native
`eval_fun_apply` rather than looking it up. Applying a datatype constructor is
left alone as well, an application of one being the Herbrand term it denotes.

`$smtx_model_eval` has a case for function application, plus cases in three
auto-generated forms:

- **Term reductions**: the operator evaluates by way of another term, e.g.
  `(bvsle x1 x2)` is `(bvsge x2 x1)`.
- **Constant folding**: the operator evaluates its arguments then applies the
  SMT-LIB operator, e.g. `(+ x1 x2)` is
  `($native_apply_2 "+" ($evaluate x1) ($evaluate x2))`.
- **Hard-coded cases**: the operator uses a custom function from the
  signature, e.g. `(select x1 x2)` is
  `($smtx_map_select ($evaluate x1) ($evaluate x2))`.

Overloaded arithmetic uses multi-case programs, and the overload naming is
reverted here: `$eoo_-.2` is recognized as SMT-LIB `-`.

## Stage 7a: smt-meta

Compiles `*.eo` to `*.smt2`. It constructs the final deep embedding — Eunoia
terms (`eo.Term`), SMT terms (`sm.Term`), SMT types (`tsm.Type`), SMT values
(`vsm.Value`), and the datatypes that model SMT values, values being disjoint
from terms — reading opaque arguments as constructor arguments and
distinguished names for Eunoia types and operators as marks for native SMT
types and operators. Non-recursive programs are optimized into `define-fun`.
It then emits, for a program under test such as `$eovc_X`, the conjecture that
the program does not get stuck for some input.

Along the way:

- Function types become ordinary applications, so `(-> T1 T2)` becomes
  `(_ (_ -> T1) T2)`.
- Eunoia pattern matching is expressed with datatype selectors and testers.
- The symbols stage 6 introduced for the embedding, `$native_apply_N` and
  `$native_type_N`, are given their meaning.
- Remaining `eo::define` and `define` commands are inlined, and an axiom is
  emitted for `eo::hash`.
- `:opaque` on user symbols becomes part of the embedding. For example
  ```
  (declare-parameterized-const @const ((id Int :opaque) (T Type :opaque)) T)
  ```
  becomes the arity-2 constructor
  ```
  (eo.@const (eo.@const.arg1 Int) (eo.@const.arg2 eo.Term))
  ```
  whereas
  ```
  (declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
  ```
  becomes the nullary constructor `(eo.and)`.

`smt_meta_sygus.{h,cpp}` emits an alternative `*.sy` file, with a well-typed
grammar, for SyGuS solvers.

One thing this stage does not establish is the well-foundedness of Eunoia
programs, which is why it can report a spurious unsoundness.

## Stage 7b: lean-meta

Compiles `*.eo` to `*.lean`, under the same opaque-argument and native-name
policy as stage 7a, and constructs correctness statements and proof stubs
for the individual rules. The downstream development proves these and connects
them to its checker theorem. `linear_patterns.{h,cpp}` linearizes
repeated variables in Eunoia patterns first, since Lean will not accept them
directly.

Lean rejects any Eunoia program it cannot see is terminating, so termination
obligations surface here rather than being assumed away. No measure the
compiler could guess would do, so the clause is stated as the Lean text it is:
a program says it with `:lean` in the configuration, and the compiler gathers
the clauses into `tools/eoc/out/smt_termination.lean` for the embedding's own
programs and `tools/eoc/out/user_termination.lean` for the input's, the second
being what `--lean-config` names. This stage appends each to the definition of
the program it belongs to.

## The Lean result

Compiling `Cpc.eo` through stage 7b produces calculus modules for a Lean
package. The checker and specification are connected by the downstream
soundness proof. As of 2026-09-18, Logos states that proof in
`Cpc/Proofs/Checker.lean`, with conclusion
`eo_satisfiability (argListAssumes F) false` under translation side conditions
and a successful `eo_is_refutation F pf` check. `argListAssumes` connects the
assumption list to a formula of CPC.

The assumptions arrive as a `CArgList`, the same list type the embedding
uses for rule arguments. The generated checker does not require a conjunction
symbol in every calculus. Connecting that list to a proposition about a concrete
input is work for the downstream development.

As of 2026-09-18, the [Logos README](https://github.com/ajreynol/logos#correctness)
describes its executable's theorem, checked side conditions and remaining
assumptions. Generated statements and per-rule proof stubs here do not supply
that theorem. The driver writes modules for a downstream package and does not
prove them or build the package.

### What this compilation does not cover

- **Proof-level lambda.** `development-cpc.eos` excludes `lambda`, related
  helper methods and `beta-reduce` explicitly. Exclusions are not closed under
  dependency automatically.
- **Parametric datatypes.** The model embedding's datatype declarations have
  no type parameters. A source signature accepted by Ethos can therefore be
  outside this compiler's model.
- **Front-end equivalence.** A proof about a generated checker does not prove
  that Ethos's parser or C++ implementation implements it. The behavior of a
  downstream text parser is a separate obligation as well.

## Known gaps

- Well-foundedness of Eunoia programs is not established, so stage 7a can
  report spurious unsoundness.
- `eo::typeof` approximates rather than reproduces Eunoia's internal type
  system (stage 5).
- The interpretation of the proof producer, its signature and the checker
  must agree. This pipeline does not check that agreement end to end.
