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
against the CPC signature, `Cpc.eo`. Stages 5 to 8 compile `Cpc.eo` itself
into a verification condition or a Lean theorem, which is what establishes
that the rules the checker applies are sound. Stages 1 to 4 run on every
query; stages 5 to 8 run offline, per proof rule.

Three code bases are involved. Only ethos is this repository:

| Code base | Role |
| --- | --- |
| cvc5 | solves the query and prints a CPC proof |
| ethos (this repository) | defines CPC in Eunoia, checks proofs against it, and compiles it |
| Logos | the Lean development in which the checker is proved correct |

Sections marked **(cvc5)** describe files in the cvc5 repository.

Stages 5 to 8 are the `ethos-eoc` binary, built from the standalone project in
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

Handled here:

- `let` as a parsing construct, not a binder.
- Global variable semantics: variables are unique up to their name and type.
  How this relates to SMT-LIB is unresolved.
- Numerals read as decimals in logics without integers.
- `:named`.

## Stage 2: cvc5 API (cvc5)

Handled here:

- Desugaring of `:chainable` and some `:left-assoc` / `:right-assoc`
  operators. This desugaring is mirrored in the CPC signature and in the ethos
  parser, so the three must be kept in step.

## Stage 3: cvc5 internals to CPC proof (cvc5)

Handled when turning the input into proof assumptions (`solver_engine.cpp`):

- `define-fun-rec` desugared to `declare-fun` plus an asserted `forall`.
- Mixed arithmetic is silently eliminated.

Handled in the proof printer:

- `match` desugared to `ite`.
- Some floating-point operators renamed.
- Currying of `ProofRule::SCOPE`.

## Stage 4: the ethos parser and checker

Handled here:

- Operator properties: `:right-assoc-nil`, `:right-assoc`, `:left-assoc-nil`,
  `:left-assoc`, `:right-assoc-non-singleton-nil`,
  `:left-assoc-non-singleton-nil`, `:chainable`, `:pairwise`, `:arg-list`,
  `:binder`, `:let-binder`.
- Desugaring of n-ary literal operations to binary, e.g. `(eo::add a b c)`
  becomes `(eo::add (eo::add a b) c)`.

Ethos then checks the proof. A `checked` verdict rests on 10,261 lines of C++
in `src/`, on GMP, and on `Cpc.eo` itself. The remaining stages are about that
last dependency.

## The deep embedding

Stages 5 to 8 share one target. A datatype `eo.Term` is declared with builtin
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
the rule is unsound. `$eovc_X` is what stage 7 verifies.

Relies on `plugins/desugar/`: `desugar.{h,cpp}`, the `eo_desugar.eo` template,
`native_embed.eo` (references to native SMT types, integer-pair encodings that
mimic parametric bitvector operations, SMT datatypes and constructors), and
`eo_desugar_native.eo` (the SMT-like builtins of Eunoia, and the declarations
of the SMT-LIB deep embedding). Optionally `plugins/trim_defs/`, which slices
the signature down so the resulting VCs stay manageable, and
`desugar_checker.{h,cpp}` with `eo_desugar_checker.eo` for the executable
checker.

Handled here:

- `define` commands inlined. Each definition is re-emitted as `$parse_<name>`,
  consumed only by stage 8 to build the generated proof parser's tables.
  Definitions whose own name starts with `$` are signature helpers and are not
  preserved.
- Optionally, flattening of evaluation: evaluation nested inside ordinary
  applications is lifted, so stuckness propagates eagerly through ordinary
  constant applications, and each `eo::requires` and `eo::ite` becomes a
  program.
- `declare-rule`: the proof type is handled as part of generating `$eovc_X`.
- `declare-consts`: `$eo_lit_type_Numeral`, `$eo_lit_type_Rational`,
  `$eo_lit_type_String`, `$eo_lit_type_Binary` as references to builtin types.
- Operator overloading, via the `$eoo_X.N` naming convention.
- Ambiguously typed functions become unambiguous functions taking an opaque
  type argument, with a helper program invoked on that type. So
  `(as nil (List Int))` becomes the opaque application `(nil (List Int))`.
- Desugaring of `eo::cons`; the `eo::list_*` family (`list_len`,
  `list_concat`, `list_nth`, `list_find`, `list_rev`, `list_erase`,
  `list_erase_all`, `list_setof`, `list_minclude`, `list_meq`); `eo::nil`,
  with a case auto-generated for each `:right-assoc-nil` and `:left-assoc-nil`
  operator; the user-defined cases of `eo::dt_constructors` and
  `eo::dt_selectors`; and the user-defined cases of `eo::typeof`.
- `eo::typeof` *approximates* Eunoia's internal type system by monomorphizing
  partial applications: there is a type rule for `(= x)`, not for `=`. A case
  is auto-generated for every user symbol, into `$eo_typeof_main`.
- `declare-datatype` and `declare-datatypes` are eliminated into ordinary types
  and constants. Datatype, constructor and selector semantics survive as the
  auto-generated `eo::dt_constructors` and `eo::dt_selectors` cases.

## Stage 6: model-smt

Compiles `*.eo` to `*.eo`, adding the definition of `$eo_model_sat`: SMT-LIB
model semantics, written in Eunoia.

The SMT-LIB signature is not hardcoded in C++. It is written directly in the
deep embedding in a definitions file, `plugins/model_smt/cpc_defs.eo`, passed
with `--defs`. For each symbol `X` that file gives the embedding constructor
`$emb_sm.X` and its macro, the cases `X` contributes to `$smtx_typeof` and to
the evaluation program `$smtx_model_eval`, and the auxiliary programs those
cases call. `defs_reader.{h,cpp}` reads the file as *text* blocks, each opened
by a `; -- X` line, and concatenates the cases into the aggregate programs,
copying everything else through unchanged. Reading it as text rather than as
terms is what stops the embedding definitions from being expanded on the way.
The same file carries `eoc-exclude` directives naming the rules, methods and
symbols to leave out of a compilation.

`plugins/model_smt/smt_defs.eo` is a further signature written the same way,
not yet included by anything.

What stays in `plugins/model_smt/model_smt.eo` is the embedding itself: the
literals, the binders, the application and datatype constructors, the two
builtins `$sm_=` and `$sm_ite`, the operations the embedding has of its own,
and the default case of each aggregate.

Handled here:

- Reduction of Eunoia builtins to SMT-LIB literal semantics: `eo::eq`;
  `eo::not`, `eo::and`, `eo::or`, `eo::xor`; `eo::add`, `eo::mul`, `eo::qdiv`,
  `eo::zdiv`, `eo::zmod`, `eo::is_neg`, `eo::neg`; `eo::len`, `eo::concat`,
  `eo::extract`, `eo::find`; `eo::to_z`, `eo::to_q`, `eo::to_bin`, `eo::to_str`;
  and `eo::var`, `eo::nameof`, which represent variables as the constant
  `$eot_Var`.
- Macros definable in terms of those, done here rather than in stage 5 so that
  desugaring never forward-references `eo::`: `eo::is_eq`, `eo::is_z`,
  `eo::is_q`, `eo::is_bin`, `eo::is_str`, `eo::is_bool`, `eo::is_var`,
  `eo::gt`, `eo::cmp`.
- `eo::typeof` completed, with literal types and the type of variables
  (`$eot_Var`), referring back to `$eo_typeof_main`.
- `eo::is_ok`, which reasons about the deep embedding: `$eo_is_ok` asks whether
  the term under test embeds as `eo.Stuck`.
- SMT-LIB semantics proper: a map utility for array and function values, with
  lookup and canonical update, specialized for sets; a sequence utility for
  sequence values; the core evaluation semantics `$smtx_model_eval`; and
  `$smtx_type_default`, which returns the first term of a finite type.

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

## Stage 7: smt-meta

Compiles `*.eo` to `*.smt2`. Constructs the final deep embedding: Eunoia terms
(`eo.Term`), SMT terms (`sm.Term`), SMT types (`tsm.Type`), SMT values
(`vsm.Value`), and the datatypes that model SMT values. Values are disjoint
from terms.

It reads opaque arguments as constructor arguments, and distinguished names for
Eunoia types and operators as marks for native SMT types and operators.
Non-recursive programs are optimized into `define-fun`. It then emits, for a
program under test such as `$eovc_X`, the conjecture that the program does not
get stuck for some input.

Handled here:

- Function types become ordinary applications: `(-> T1 T2)` becomes
  `(_ (_ -> T1) T2)`.
- Eunoia pattern matching in terms of datatype selectors and testers.
- The symbols stage 6 introduced for the embedding, `$native_apply_N` and
  `$native_type_N`.
- Remaining `eo::define` and `define` commands inlined.
- An axiom for `eo::hash`.
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

Not handled: well-foundedness of Eunoia programs. Because the encoding does not
establish it, this stage can report a spurious unsoundness.

## Stage 8: lean-meta

Compiles `*.eo` to `*.lean`, under the same opaque-argument and native-name
policy as stage 7. It constructs correctness theorems for the individual rules
and for the checker as a whole. `linear_patterns.{h,cpp}` linearizes repeated
variables in Eunoia patterns first, since Lean will not accept them directly.

Lean will reject any Eunoia program it cannot see is terminating, so
termination obligations surface here. What the compiler cannot derive is
supplied per signature with `--lean-config`; for CPC that is
`plugins/lean_meta/cpc_termination.lean`.

## The Lean result

Compiling `Cpc.eo` through stage 8 produces the Lean package Logos, whose
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

## Known gaps

- Well-foundedness of Eunoia programs is not established, so stage 7 can report
  spurious unsoundness.
- `eo::typeof` approximates rather than reproduces Eunoia's internal type
  system (stage 5).
- The `:chainable` and assoc desugarings are mirrored in the cvc5 API, the CPC
  signature and the ethos parser, with nothing checking that the three agree
  (stages 2 and 4).
- Mixed arithmetic is eliminated silently on the way into proof assumptions
  (stage 3).
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

### Stages 5, 6 and 8: Eunoia to Lean

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
| `cpc_defs.eo`, the SMT-LIB signature | 1,596 EO |
| **Eunoia total** | **3,938** |
| Lean templates, `plugins/lean_meta/*.lean` | 1,102 Lean |

`plugins/model_smt/smt_defs.eo` is a further 3,434 lines of Eunoia, not yet
included by anything.

### Stage 7: Eunoia to SMT-LIB and SyGuS

Stages 5 and 6 above are shared; this backend adds:

| Component | LOC |
| --- | --- |
| `smt_meta_reduce.{h,cpp}` | 945 C++ |
| `smt_meta_sygus.{h,cpp}` | 497 C++ |
| `smt_meta/utils.{h,cpp}` | 62 C++ |
| `trim_defs.{h,cpp}` | 756 C++ |
| `smt_meta.smt2` template | 293 SMT2 |

### Generated Logos

The Lean package compiled from `Cpc.eo` by the `lean --all` command above,
using the exclusions in `cpc_defs.eo`.

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
