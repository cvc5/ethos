# The cvc5 proof pipeline

This document summarizes how a cvc5 proof is produced, checked, and verified.
It covers one pipeline:

```
input.smt2 -> cvc5 parser -> cvc5 API -> cvc5 internals -> proof.cpc
                                                              |
                                                Cpc.eo -> ethos -> accept/reject
                                                   |
                                                   +-> desugar -> model-smt -+-> rule.smt2
                                                                             +-> Logos (Lean)
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
python3 tools/eoc/driver.py vc --build-dir build-eoc <input.eo> <proof-rule>

# the whole CPC signature, compiled to Lean
python3 tools/eoc/driver.py lean --build-dir build-eoc --all \
  --defs=plugins/model_smt/cpc_defs.eo \
  --lean-config=plugins/lean_meta/cpc_termination.lean \
  <cvc5>/proofs/eo/cpc/Cpc.eo
```

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
template, `native_embed.eo` (references to native SMT types, integer-pair
encodings that mimic parametric bitvector operations, SMT datatypes and
constructors), and `eo_desugar_native.eo` (the SMT-like builtins of Eunoia,
and the declarations of the SMT-LIB deep embedding). Two parts are optional:
`plugins/trim_defs/`, which slices the signature down so the resulting VCs stay
manageable, and `desugar_checker.{h,cpp}` with `eo_desugar_checker.eo`, which
desugars the executable checker.

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
| `plugins/model_smt/smt_defs.eo` | the SMT-LIB signature, which is the target and so is fixed |
| `--defs <file>`, e.g. `plugins/model_smt/cpc_defs.eo` | how the symbols of the input transform into it |

Each is a sequence of blocks, one per symbol, opened by a `; -- X` line. For a
symbol `X`, `smt_defs.eo` gives the embedding constructor `$emb_sm.X` and the
macro `$sm_X`, the cases `X` contributes to `$smtx_typeof` and to the
evaluation program `$smtx_model_eval` (as `$eoc_typeof_X` and `$eoc_eval_X`),
and the auxiliary programs those cases call. `cpc_defs.eo` gives
`$eoc_transform_X`, the cases `X` contributes to `$eo_to_smt`, and
`$eoc_transform_type_X` for a type constructor.

`defs_reader.{h,cpp}` reads a file as *text* blocks and splices the cases into
the aggregate programs, copying everything else through unchanged. Reading text
rather than terms is what stops the embedding definitions from being expanded
on the way. The plugin algorithms hold no per-symbol semantics: they take the
blocks the input needs together with the blocks those name, put what each says
where it belongs in the template, and check that no declared symbol was left
without a meaning.

A block may also say that the compilation has no place for its symbol, by
giving `eoc-exclude` directives instead of a model. The desugar stage reads
those and drops what they name.

What stays in `plugins/model_smt/model_smt.eo` is the embedding itself: the
literals, the binders, the application and datatype constructors, the two
builtins `$sm_=` and `$sm_ite`, the operations the embedding has of its own,
and the default case of each aggregate.

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

The SMT-LIB semantics proper consist of a map utility for array and function
values, with lookup and canonical update, specialized for sets; a sequence
utility for sequence values; the core evaluation semantics `$smtx_model_eval`;
and `$smtx_type_default`, which returns the first term of a finite type.

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
obligations surface here rather than being assumed away. What the compiler
cannot derive is supplied per signature with `--lean-config`; for CPC that is
`plugins/lean_meta/cpc_termination.lean`.

## The Lean result

Compiling `Cpc.eo` through stage 7b produces the Lean package Logos, whose
central obligation is stated in the specification module:

```lean
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
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

The trusted computing base is the import closure of the specification module:
everything except the checker, the parser and the rule lemmas. That is 2,696
lines of Lean out of 27,158 generated, as the appendix breaks down.

### What Logos does not cover

Logos checks a sublanguage of what ethos checks, so a proof ethos accepts is
not necessarily one Logos accepts.

- **No `lambda` or `beta-reduce`.** SMT-LIB gives a proof-level binder no
  meaning, so `cpc_defs.eo` excludes the symbol `lambda`, the methods
  `$get_lambda_type`, `$beta_reduce_type` and `$beta_reduce`, and the rule
  `beta-reduce`.
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

## Appendix: component sizes

Code lines, excluding blank and comment lines, measured 2026-08-26 with cloc
2.11:

```bash
cloc --force-lang=Lisp,eo --force-lang=Lisp,smt2 <files>
```

A count for a C++ component is its implementation plus its header.

### Shared

| Component | LOC |
| --- | --- |
| ethos core, `src/` | 10,261 C++ |
| `src/plugin.h`, the callback interface | 64 C++ |
| `plugins/std_plugin`, `meta_reduce_plugin`, `utils` | 782 C++ |
| `plugins/main_eoc.cpp` | 206 C++ |
| `tools/eoc/driver.py` | 823 Python |

### Stages 5, 6 and 7b: Eunoia to Lean

| Component | LOC |
| --- | --- |
| `desugar.{h,cpp}` | 1,279 C++ |
| `desugar_checker.{h,cpp}` | 153 C++ |
| `model_smt.{h,cpp}` | 227 C++ |
| `defs_reader.{h,cpp}` | 447 C++ |
| `linear_patterns.{h,cpp}` | 176 C++ |
| `lean_meta_reduce.{h,cpp}` | 1,815 C++ |
| shared | 782 C++ |
| **C++ total** | **4,879** |
| `native_embed.eo` | 142 EO |
| `eo_desugar.eo` | 394 EO |
| `eo_desugar_native.eo` | 592 EO |
| `eo_desugar_checker.eo` | 204 EO |
| `model_smt.eo` | 1,010 EO |
| `smt_defs.eo`, the SMT-LIB signature | 3,434 EO |
| `cpc_defs.eo`, the CPC signature | 1,596 EO |
| **Eunoia total** | **7,372** |
| Lean templates, `plugins/lean_meta/*.lean` | 1,102 Lean |

### Stage 7a: Eunoia to SMT-LIB and SyGuS

Stages 5 and 6 above are shared; this backend adds:

| Component | LOC |
| --- | --- |
| `smt_meta_reduce.{h,cpp}` | 945 C++ |
| `smt_meta_sygus.{h,cpp}` | 497 C++ |
| `smt_meta/utils.{h,cpp}` | 62 C++ |
| `trim_defs.{h,cpp}` | 756 C++ |
| `smt_meta.smt2` template | 293 SMT2 |

### Generated Logos

The Lean package compiled from `Cpc.eo` by the `lean --all` command above.

| Module | LOC | In TCB |
| --- | --- | --- |
| `SmtEval.lean`, evaluation utilities | 140 | yes |
| `LogosTerm.lean`, term datatype | 247 | yes |
| `SmtModel.lean` | 1,598 | yes |
| `SmtModelDefs.lean` | 226 | yes |
| `SmtValueOrder.lean` | 98 | yes |
| `Spec.lean`, Eunoia to SMT correspondence | 387 | yes |
| `Logos.lean`, the checker | 8,215 | no |
| `Parser.lean`, proof parser configuration | 1,999 | no |
| `RuleLemmas.lean`, rule lemma statements | 3,607 | no |
| `Rules/*.lean`, 591 per-rule files | 10,641 | no |
| **Total** | **27,158** | |

Trusted computing base: 140 + 247 + 1,598 + 226 + 98 + 387 = 2,696 lines of
Lean.
