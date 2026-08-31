# The cvc5 proof pipeline

This document summarizes how a cvc5 proof is produced, checked, and verified.
It covers one pipeline:

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
into a verification condition or a Lean theorem, which is what establishes
that the rules the checker applies are sound. Stages 1 to 4 run on every
query; stages 5 to 7 run offline, per proof rule.

Three code bases are involved. Only ethos is this repository:

| Code base | Role |
| --- | --- |
| cvc5 | solves the query and prints a CPC proof |
| ethos (this repository) | defines CPC in Eunoia, checks proofs against it, and compiles it |
| Logos | the Lean development in which the checker is proved correct |

Sections marked **(cvc5)** describe files in the cvc5 repository.

Stages 5 to 7 are the `ethos-eoc` binary, built from the standalone project in
[`plugins/`](plugins/) and driven by
[`tools/eoc/driver.py`](tools/eoc/driver.py):

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
configuration the driver compiles before any stage runs, see stage 6. The
wrappers in [`tools/eoc/cpc/`](tools/eoc/cpc/) pass them for the default CPC
input, so `run_gen_vc <rule>` and `run_gen_lean_all` are the same two commands
with the paths filled in.

See [`tools/eoc/README.md`](tools/eoc/README.md) for the full driver
interface.

## Stage 1: cvc5 parsing (cvc5)

The parser is where the surface syntax of the input is resolved. It settles:

- `let` as a parsing construct, not a binder.
- Global variable semantics: variables are unique up to their name and type.
  How this relates to SMT-LIB is unresolved.
- Numerals read as decimals in logics without integers.
- `:named`.

## Stage 2: cvc5 API (cvc5)

The API desugars `:chainable` and some `:left-assoc` and `:right-assoc`
operators. The CPC signature and the ethos parser mirror this desugaring, so
the three have to be kept in step.

## Stage 3: cvc5 internals to CPC proof (cvc5)

Two places in cvc5 change the problem on the way to a proof. Turning the input
into proof assumptions (`solver_engine.cpp`) desugars `define-fun-rec` into a
`declare-fun` plus an asserted `forall`. The proof printer then desugars
`match` into `ite`, renames some floating-point operators, and curries
`ProofRule::SCOPE`.

## Stage 4: the ethos parser and checker

The parser applies the operator properties declared in the signature —
`:right-assoc-nil`, `:right-assoc`, `:left-assoc-nil`, `:left-assoc`,
`:right-assoc-non-singleton-nil`, `:left-assoc-non-singleton-nil`,
`:chainable`, `:pairwise`, `:arg-list`, `:binder` and `:let-binder` — and
lowers n-ary literal operations to binary ones, so that `(eo::add a b c)`
becomes `(eo::add (eo::add a b) c)`.

Ethos then checks the proof. A `checked` verdict rests on 10,261 lines of C++
in `src/`, on GMP, and on `Cpc.eo` itself. The remaining stages are about that
last dependency.

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
SMT backend means there is no such term.

Terms carry a *meta-kind* saying what their embedding is: a Eunoia term, an SMT
term, an SMT type, an SMT value, a map or sequence value, a builtin, a proof,
a checker rule or command. Types applied to `$native_embed_eo`,
`$native_embed_smt` or `$native_embed_checker` in the Eunoia templates declare
which of the three layers a datatype belongs to. See `MetaKind` in
[`plugins/utils.h`](plugins/utils.h).

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
under [`tools/eoc/semantics/`](tools/eoc/semantics/), which
`tools/eoc/sem_compile.py` compiles into them; the driver runs it before any
stage, so the two are never out of step with what the stage reads.

| Configuration | Compiles to |
| --- | --- |
| `semantics/smt.eos`, named by `--smt-semantics` | `smt_defs.eo`, `smt_termination.lean` |
| `semantics/development-cpc.eos`, named by `--semantics` | `user_defs.eo`, `user_termination.lean` |
| `plugins/desugar/natives.eos` | `native_defs.eo`, the natives the embedding calls |
| `plugins/model_smt/model_smt.eos` | the head of each signature above, which says how the stage takes it apart |
| `plugins/lean_meta/lean.eos` | `lean_native.lean`, the native layer of stage 7b |
| `plugins/smt_meta/smt-vc.eos` | `smt_vc_native.smt2`, the native layer of stage 7a |

The first two a run may name another of; the rest are fixed, since they say
what the embedding is rather than what a signature means.

`smt.eos` is the target, so every input is compiled through it and nothing
about an input is asked of it. `development-cpc.eos` is a *test*, kept so that
the compiler and the stages after it have a real signature to run over; **the
official semantics of CPC lives in the Logos repository**, and that is what a
run meaning to say something about CPC names with `--semantics`. A set that
lives in another tree compiles beside itself, so running against the official
one leaves this tree alone.

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
what the embedding *is*. `tools/eoc/semantics/README.md` is the reference for
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
`tools/eoc/sem_target.py`, and this stage needs no change and no rebuild.

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
policy as stage 7a, and constructs correctness theorems for the individual
rules and for the checker as a whole. `linear_patterns.{h,cpp}` linearizes
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

Compiling `Cpc.eo` through stage 7b produces the Lean package Logos, whose
central obligation is stated in the specification module:

```lean
theorem correct___eo_is_refutation (F : CArgList) (pf : CCmdList) :
  TranslatableAssumptionList F ->
  CmdListTranslationOk pf ->
  (eo_is_refutation F pf) ->
  eo_satisfiability F false
```

`eo_is_refutation` invokes the generated checker, and `eo_satisfiability` is
defined through the Eunoia-to-SMT translation and the SMT model semantics:
`eo_satisfiability t b` is `smt_satisfiability (__eo_to_smt t) b`. The
hypotheses `TranslatableAssumptionList` and `CmdListTranslationOk` are stated
in the Logos development, not generated from this repository.

The assumptions arrive as a `CArgList`, the list of the embedding that a rule's
arguments already arrive in, rather than as a conjunction of the calculus. A
calculus need not have a conjunction -- the checker used to name `and`, which
is a symbol a signature declares and not one the embedding has, so a calculus
without it could not be compiled at all. Nothing in the generated checker now
names a symbol of any calculus. Logos states `eo_satisfiability` of a single
term, so what the theorem relates the list to is the Logos development's own
to say.

The trusted computing base is the import closure of the specification module:
everything except the checker, the parser and the rule lemmas. That is 2,680
lines of Lean out of 27,139 generated, as the appendix breaks down.

### What Logos does not cover

Logos checks a sublanguage of what ethos checks, so a proof ethos accepts is
not necessarily one Logos accepts.

- **No `lambda` or `beta-reduce`.** SMT-LIB gives a proof-level binder no
  meaning, so `development-cpc.eos` writes `:exclude` on the symbol `lambda`,
  on the methods `$get_lambda_type`, `$beta_reduce_type` and `$beta_reduce`,
  and on the rule `beta-reduce`. No dependency closure is computed, so each
  says so where it stands.
- **No `define-fun`.** The generated command language is `assume_push`,
  `check_proven`, `step` and `step_pop`; there is no command that introduces a
  definition, so a proof that defines terms is out of scope.
- **No parametric datatypes.** A datatype in the embedding is a name and a
  list of constructors, with no place for type parameters, so datatypes are
  monomorphic.

## Known gaps

- Well-foundedness of Eunoia programs is not established, so stage 7a can
  report spurious unsoundness.
- `eo::typeof` approximates rather than reproduces Eunoia's internal type
  system (stage 5).
- The `:chainable` and assoc desugarings are mirrored in the cvc5 API, the CPC
  signature and the ethos parser, with nothing checking that the three agree
  (stages 2 and 4).
- How cvc5's global variable semantics relates to SMT-LIB's is unresolved
  (stage 1).

## Future directions

- Fuzz ethos to confirm it stays synchronized with the desugaring semantics.
- An Isabelle backend, and possibly Agda or Dedukti backends.
- Parametric bitvectors in cvc5, to discharge the generated VCs.
- Logos as a reimplementation of ethos whose native language is desugared
  `*.eo`, formally verified so as to absorb some stages of this pipeline.
- Telos: an SMT solver API running cvc5 to the proof API to ethos or Logos.
- Alethe to Eunoia.
- `eo::native` in the front end of ethos, so that a signature may name an
  operation its target has and Eunoia does not -- a Lean method, an SMT-LIB
  function -- rather than the natives being a closed list only the compiler may
  extend. It is the one direction that shortens the loop a *calculus author* is
  in, and it is what makes checking a target's native coverage a requirement
  rather than a tidy-up. See the stretch goal in
  [`docs/README.md`](docs/README.md).

## Appendix: component sizes

Code lines, excluding blank and comment lines, measured 2026-08-30 with cloc
2.06:

```bash
cloc --force-lang=Lisp,eo --force-lang=Lisp,eos --force-lang=Lisp,smt2 <files>
```

A count for a C++ component is its implementation plus its header.

### Shared

| Component | LOC |
| --- | --- |
| ethos core, `src/` | 10,278 C++ |
| `src/plugin.h`, the callback interface | 64 C++ |
| `plugins/std_plugin`, `meta_reduce_plugin`, `native_layer`, `utils` | 992 C++ |
| `plugins/main_eoc.cpp` | 220 C++ |
| `tools/eoc/driver.py` | 912 Python |
| `tools/eoc/sem_{lang,target,compile}.py`, the configuration compiler | 2,026 Python |
| `tools/eoc/report.py`, `test/regress.py` | 148 Python |

### Stages 5, 6 and 7b: Eunoia to Lean

| Component | LOC |
| --- | --- |
| `desugar.{h,cpp}` | 1,347 C++ |
| `desugar_checker.{h,cpp}` | 161 C++ |
| `model_smt.{h,cpp}` | 264 C++ |
| `defs_reader.{h,cpp}` | 612 C++ |
| `linear_patterns.{h,cpp}` | 176 C++ |
| `lean_meta_reduce.{h,cpp}` | 1,878 C++ |
| shared | 992 C++ |
| **C++ total** | **5,430** |
| `native_embed.eo` | 44 EO |
| `eo_desugar.eo` | 391 EO |
| `eo_desugar_native.eo` | 576 EO |
| `eo_desugar_checker.eo` | 204 EO |
| `model_smt.eo`, the embedding | 336 EO |
| **Eunoia total** | **1,551** |
| Lean templates, `plugins/lean_meta/*.lean` | 494 Lean |

### Stage 7a: Eunoia to SMT-LIB and SyGuS

Stages 5 and 6 above are shared; this backend adds:

| Component | LOC |
| --- | --- |
| `smt_meta_reduce.{h,cpp}` | 957 C++ |
| `smt_meta_sygus.{h,cpp}` | 487 C++ |
| `smt_meta/utils.{h,cpp}` | 62 C++ |
| `trim_defs.{h,cpp}` | 757 C++ |
| `smt_meta.smt2` template | 145 SMT2 |

### The configuration

What the pipeline knows about a theory, a native or the shape of what it
writes is stated once, in a configuration set, and compiled. This is the
measure worth watching: a line here is a line someone writes, and a line in the
right-hand column is one nobody maintains.

| Written by hand | LOC | Compiles to | LOC |
| --- | --- | --- | --- |
| `semantics/smt.eos`, the SMT-LIB semantics | 1,547 | `smt_defs.eo`, `smt_termination.lean` | 4,443 |
| `semantics/development-cpc.eos`, the semantics of an input | 615 | `user_defs.eo`, `user_termination.lean` | 1,624 |
| `desugar/natives.eos`, the natives and the primitive types | 74 | `native_defs.eo` | 123 |
| `model_smt/model_smt.eos`, the aggregates and the datatypes | 73 | the head of the two signatures | — |
| `lean_meta/lean.eos`, the native layer of stage 7b | 649 | `lean_native.lean` | 482 |
| `smt_meta/smt-vc.eos`, the native layer of stage 7a | 227 | `smt_vc_native.smt2` | 152 |
| **Total** | **3,185** | | **6,824** |

Against the declarative material that is still written out by hand -- 1,570
lines of Eunoia, 550 of Lean template and 145 of SMT-LIB template, 2,265 in all
-- **58%** of what the pipeline is told is now configuration rather than
something maintained in the form the stages read.

Of those 1,570 lines of Eunoia, **1,215 are the Eunoia embedding** --
`eo_desugar*.eo` and `native_embed.eo`, which say what Eunoia *is* and are
hand-written for the reason a language's own definition is. The remaining 355
are `model_smt.eo`, the last hand-written Eunoia that describes a *target*
rather than the language. What is left in it is the ten programs a
configuration contributes cases to, and the term constructors of the
embedding -- the binders, the application and the ones carrying a name and a
type. Those are not left over: a `define-symbol` says what a symbol evaluates
to with each argument standing for its *value*, and these are exactly the
constructors whose evaluation is not compositional, so a case of one cannot be
written that way.

None of the right-hand column is checked in; see the `tools/eoc/out/` line of
`.gitignore`. `sem_compile.py --check` says it holds what compiling writes, and
`tools/eoc/test/regress.py` says the pipeline still writes the same bytes for a
signature of this tree.

#### What moved, and what it bought

51% of what the pipeline is told was configuration and 58% is, and where that
came from matters more than the number. What moved is *which* things a stage
holds a name of:

| | before | after |
| --- | --: | --: |
| `native_embed.eo`, the layer's own file | 76 EO | **44 EO** |
| definitions written by hand in it | 28 | **0** |
| constructor and marker names hardcoded in the model-smt stage | 11 | **0** |
| constructors of the embedding's datatypes declared in `model_smt.eo` | 20 | **0** |
| programs over datatypes written in `model_smt.eo` | 25 | **2** |
| helper programs in `model_smt.eo` | 37 | **7** |
| `model_smt.eo` | 697 EO | **336 EO** |
| datatypes of the embedding whose Lean inductive is written by hand | 9 | **3** |
| index arities the embedding can express | exactly 3 | **as many as declared** |

Three changes account for it, and each removed a *kind* of hardcoding rather
than an instance:

- **The natives say what they are.** `natives.eos` declares the primitive
  types as well as the natives written over them, and a native that forwards
  to nothing says what it is under `:is`, so `native_embed.eo` holds
  declarations and no definitions at all. The rename that went with it --
  `<numeral>` for what a backend calls `Int` -- caught a live inconsistency:
  the rational natives were typed `$native_Real` in Eunoia while both backends
  implement only `Rat`, which nothing had reason to notice because a native's
  return type is not checked.
- **The UserOp ladder is as long as the calculus.** `$emb_UOp<n>` is emitted
  per index arity the signature uses rather than fixed at three, so a
  calculus that indexes nothing carries no `UserOp<n>` and none of the cases
  every generated function owed them, and one that indexes four ways compiles
  for the first time.
- **The backend writes no datatype it was told about.** The inductive a
  datatype of the embedding prints as, and its ordering key, are generated from
  the constructors the target declares -- the map, the sequence, the regular
  language and the three a datatype declaration is made of, which were written
  by hand in `lean_meta_smt_model_defs.lean` and had to be kept in step with
  `smt.eos` by eye. The three left are the checker's own and the Eunoia-side
  ones, which mirror the hand-written embedding rather than a configuration.
- **The constructor families are declared.** A `declare-embed-datatype` entry
  in `model_smt.eos` says what a constructor of one of the embedding's
  datatypes is called and where it is written, and a `declare-constructor`
  says which datatype it builds. The model-smt stage holds no such name, so a
  family moves out of the template with configuration alone, and all six have:
  the term, the type and the value, and beneath them the map an array and a
  set both are, the sequence a string is, the regular language, and the three
  a datatype declaration is made of. `model_smt.eo` declares not one
  constructor now -- it says which datatypes there are and what the embedding
  *does* with them, and the ways of building one are the target's to write.
  The name of a constructor is scoped by the datatype, so the `cons` of a map
  and the `cons` of a sequence are two constructors and not a clash.
- **A datatype's semantics is where a map's already was.** The map and the
  sequence had every program over them in the target's set; the datatypes had
  25 of theirs in the template, so asking what a map's default value is read
  one file and asking it of a datatype read another, in another vocabulary.
  Those programs are now beside the constructors they are written over, each
  carrying its own termination clause rather than having one said about it
  from a `define-method` elsewhere. Two are left in the template, and for
  reasons worth recording: `$smtx_model_eval_dt_sel` and its tester are named
  under the `$smtx_model_eval_` helper prefix, which a set may not write, and
  the three `$eo_to_smt_datatype*` name `$eo_to_smt_type` outright, which a
  case may not do -- a name of the input stands for what it transforms into,
  and those programs are the transformation itself.

What none of this touches is the loop a *calculus author* is in, which is the
agility this document's sibling
[`docs/README.md`](docs/README.md) is about: nobody adds a regular language
constructor, and the datatypes above are SMT-LIB's and fixed. What it buys is
the ability to ask what a second *target* would cost, which was previously
welded into C++ and is now data.

One consequence a reader of the generated Lean will meet: moving a program from
the template to the set moves where it is *written*, so the generated modules
hold the same definitions in a different order. Every definition of a generated
CPC package was checked to be present and character-for-character what it was --
600 modules, nothing missing, added or altered -- and the same of the two
verification conditions, whose forms are the same multiset. Order is all that
moved, and Lean and SMT-LIB are both indifferent to it, but a diff of a
regenerated package is not small.

### Generated Logos

The Lean package compiled from `Cpc.eo` by the `lean --all` command above.

| Module | LOC | In TCB |
| --- | --- | --- |
| `SmtEval.lean`, evaluation utilities | 108 | yes |
| `LogosTerm.lean`, term datatype | 253 | yes |
| `SmtModel.lean` | 1,602 | yes |
| `SmtModelDefs.lean` | 230 | yes |
| `SmtValueOrder.lean` | 100 | yes |
| `Spec.lean`, Eunoia to SMT correspondence | 387 | yes |
| `Logos.lean`, the checker | 8,212 | no |
| `Parser.lean`, proof parser configuration | 1,999 | no |
| `Proofs/RuleLemmas.lean`, rule lemma statements | 3,607 | no |
| `Proofs/Rules/*.lean`, 591 per-rule files | 10,641 | no |
| **Total** | **27,139** | |

Trusted computing base: 108 + 253 + 1,602 + 230 + 100 + 387 = 2,680 lines of
Lean.
