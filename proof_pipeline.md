# How cvc5 proofs are produced, checked, and verified

This document is an executive summary of the whole cvc5 proof setup: what
happens to a query between cvc5 reading it and someone believing the answer,
and where in that path each awkward detail is dealt with.

It spans three code bases. Only the middle one is this repository:

| Code base | Role here |
| --- | --- |
| cvc5 | solves the query and prints a proof in the CPC calculus |
| ethos (this repository) | defines CPC in Eunoia, and checks proofs against it |
| Logos | the Lean development in which the checker is proved correct |

Sections marked **(cvc5)** describe files in the cvc5 repository, not in this
one.

## The two journeys

A proof travels two quite different paths, and most confusion about this setup
comes from running them together. They answer different questions.

```
  Journey 1 — every query, at solving time
  ----------------------------------------
  input.smt2 --> cvc5 parser --> cvc5 API --> cvc5 internals
                                                    |
                                                    v
                                            proof.cpc (a CPC proof)
                                                    |
                                     Cpc.eo ---> ethos ---> accept / reject


  Journey 2 — once per proof rule, offline
  ----------------------------------------
  Cpc.eo --> desugar --> model-smt --+--> smt-meta  --> rule.smt2  (unsat = good)
                                     |
                                     +--> lean-meta --> Logos      (theorem to prove)
```

**Journey 1 answers**: does this proof follow the rules written in `Cpc.eo`?
That is what `ethos` decides, and it is fast and fully automatic.

**Journey 2 answers**: are the rules written in `Cpc.eo` actually sound with
respect to SMT-LIB semantics? Journey 1 takes `Cpc.eo` entirely on trust, so
this is where that trust is earned. It is the `ethos-eoc` binary's job, it is
run offline, and it is per rule rather than per proof.

Both journeys are lossy in ways worth knowing about, which is what the rest of
this document is for.

## Journey 1: producing and checking a proof

### Stage 1: cvc5 parsing (cvc5)

Handled here:

- `let` as a parsing construct, not a binder.
- Global variable semantics: variables are unique up to their name and type.
  It is an open question how exactly this relates to SMT-LIB.
- Numerals read as decimals in logics without integers.
- `:named`.

### Stage 2: cvc5 API (cvc5)

Handled here:

- Desugaring of `:chainable` and some `:left-assoc` / `:right-assoc`
  operators. This desugaring is mirrored in the CPC signature and in the ethos
  parser, so the two must be kept in step.

### Stage 3: cvc5 internals to CPC proof (cvc5)

Handled here, when turning the input into proof assumptions
(`solver_engine.cpp`):

- `define-fun-rec` desugared to `declare-fun` plus an asserted `forall`.
- Mixed arithmetic is silently eliminated.

And in the proof printer:

- `match` desugared to `ite`.
- Some floating-point operators renamed.
- Currying of `ProofRule::SCOPE`.

### Stage 4: the ethos parser

Handled here:

- Operator properties: `:right-assoc-nil`, `:right-assoc`, `:left-assoc-nil`,
  `:left-assoc`, `:right-assoc-non-singleton-nil`,
  `:left-assoc-non-singleton-nil`, `:chainable`, `:pairwise`, `:arg-list`,
  `:binder`, `:let-binder`.
- Desugaring of n-ary literal operations to binary, e.g. `(eo::add a b c)`
  becomes `(eo::add (eo::add a b) c)`.

At this point ethos can check the proof, and Journey 1 is done. Roughly 10k
lines of C++ in `src/`, plus GMP, are what a `checked` verdict rests on,
together with `Cpc.eo` itself.

## Journey 2: verifying the CPC signature

Everything below is the `ethos-eoc` binary, built from the standalone project
in [`plugins/`](plugins/) and driven by
[`tools/eoc/driver.py`](tools/eoc/driver.py). To generate the verification
condition for one rule:

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc <input.eo> <proof-rule>
```

See [`tools/eoc/README.md`](tools/eoc/README.md) for the full driver
interface.

### The idea: a deep embedding

Both backends end in a deep embedding, and both encode a rule's correctness as
a search over that embedding:

- A datatype `eo.Term` is declared, with builtin constructors such as
  `eo.Stuck` and `eo.Apply`.
- Every constant in the Eunoia signature becomes a constructor of that
  datatype.

Under the SMT backend, Eunoia programs become uninterpreted functions and
their definitions become quantified axioms; a program that is forward declared
but never defined stays a free uninterpreted function. Under the Lean backend,
Eunoia programs become Lean definitions.

So a rule's soundness becomes a question about the *syntactic space* of Eunoia
terms: is there a term that witnesses the rule being unsound? An `unsat` from
the SMT backend says no such witness exists, which is the evidence that the
rule is sound.

Terms carry a *meta-kind* through the pipeline saying what their embedding is:
a Eunoia term, an SMT term, an SMT type, an SMT value, a map or sequence
value, a builtin, a proof, a checker rule or command. Types applied to
`$native_embed_eo`, `$native_embed_smt` or `$native_embed_checker` in the
Eunoia templates declare which of the three layers a datatype belongs to; see
`MetaKind` in [`plugins/utils.h`](plugins/utils.h).

### Stage 5: desugar

Compiles `*.eo` to `*.eo`, rewriting non-essential Eunoia features into Eunoia
programs. It emits a forward declaration of the side condition `$eo_model_sat`,
which the next stage defines.

Optionally, a proof rule is compiled to a Eunoia program `$eo_prog_X` that
operates over *formulas* rather than proofs, plus a program `$eovc_X` that
calls `$eo_model_sat` and `$eo_prog_X` and evaluates successfully exactly when
the rule is unsound. `$eovc_X` is the target the SMT backend verifies.

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
  consumed only by the Lean stage to build the generated proof parser's tables.
  Definitions whose own name starts with `$` are signature helpers and are not
  preserved.
- Optionally, flattening of evaluation: evaluation nested inside ordinary
  applications is lifted, so stuckness propagates eagerly through ordinary
  constant applications, and each `eo::requires` / `eo::ite` becomes a program.
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

### Stage 6: model-smt

Compiles `*.eo` to `*.eo`, adding the definition of `$eo_model_sat`: SMT-LIB
model semantics, written in Eunoia.

The SMT-LIB signature itself is *not* hardcoded in C++. It is written directly
in the deep embedding in a definitions file, `plugins/model_smt/cpc_defs.eo`,
passed with `--defs`. For each symbol `X` that file gives the embedding
constructor `$emb_sm.X` and its macro, the cases `X` contributes to
`$smtx_typeof` and to the evaluation program `$smtx_model_eval`, and the
auxiliary programs those cases call. `defs_reader.{h,cpp}` reads the file as
*text* blocks — a block opens at a `; -- X` line — and concatenates the cases
into the aggregate programs, copying everything else through unchanged. Reading
it as text rather than as terms is what stops the embedding definitions from
being expanded on the way. `plugins/model_smt/smt_defs.eo` is an in-progress
signature written the same way, not yet wired into the pipeline.

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
- Macros definable in terms of those, done here rather than in desugar so that
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
  `$smtx_type_default`, which enumerates the first term of a finite type.

`$smtx_model_eval` has a case for function application, plus cases in three
auto-generated forms:

- **Term reductions** — this operator evaluates by way of another term, e.g.
  `(bvsle x1 x2)` is `(bvsge x2 x1)`.
- **Constant folding** — this operator evaluates its arguments then applies the
  SMT-LIB operator, e.g. `(+ x1 x2)` is
  `($native_apply_2 "+" ($evaluate x1) ($evaluate x2))`.
- **Hard-coded cases** — this operator uses a custom function from the
  signature, e.g. `(select x1 x2)` is
  `($smtx_map_select ($evaluate x1) ($evaluate x2))`.

Overloaded arithmetic uses multi-case programs, and the overload naming is
reverted here: `$eoo_-.2` is recognized as SMT-LIB `-`.

### Stage 7a: smt-meta, the SMT-LIB and SyGuS backend

Compiles `*.eo` to `*.smt2`. Constructs the final deep embedding: Eunoia terms
(`eo.Term`), SMT terms (`sm.Term`), SMT types (`tsm.Type`), SMT values
(`vsm.Value`), and the datatypes that model SMT values. Values are disjoint
from terms.

It applies a policy that reads opaque arguments as constructor arguments, and
distinguished names for Eunoia types and operators as marks for native SMT
types and operators. Non-recursive programs are optimized into `define-fun`.
Finally it emits, for a program under test such as `$eovc_X`, the conjecture
that the program does not get stuck for some input. `unsat` means no such input
exists, which is the evidence of soundness.

Handled here:

- Function types become ordinary applications: `(-> T1 T2)` becomes
  `(_ (_ -> T1) T2)`.
- Eunoia pattern matching in terms of datatype selectors and testers.
- The symbols the model-smt stage introduced for the embedding,
  `$native_apply_N` and `$native_type_N`.
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

**Not handled**: well-foundedness of Eunoia programs. Because the encoding does
not establish it, this stage can report a spurious unsoundness.

### Stage 7b: lean-meta, the Lean backend

Compiles `*.eo` to `*.lean`, under the same opaque-argument and native-name
policy as smt-meta. It constructs correctness theorems for the individual rules
and for the checker as a whole. `linear_patterns.{h,cpp}` linearizes repeated
variables in Eunoia patterns first, since Lean will not accept them directly.

Lean will complain about any Eunoia program it cannot see is terminating, so
termination obligations surface at this stage rather than being assumed away.

## The Lean end state

Compiling `Cpc.eo` through the Lean backend produces a Lean package, Logos,
whose central obligation is stated in the specification module:

```lean
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  TranslatableAssumptionList F ->
  CmdListTranslationOk pf ->
  (eo_is_refutation F pf) ->
  eo_satisfiability F false
```

Here `eo_is_refutation` invokes the generated checker, and `eo_satisfiability`
is defined through the Eunoia-to-SMT translation and the SMT model semantics —
`eo_satisfiability t b` is `smt_satisfiability (__eo_to_smt t) b`. The
hypotheses `TranslatableAssumptionList` and `CmdListTranslationOk` are stated
in the Logos development, not generated from this repository.

The trusted computing base is the import closure of the specification module:
everything *except* the checker, the parser and the rule lemmas. That is the
evaluation utilities, the term datatype, the SMT model semantics and the
specification itself, on the order of 2,700 lines of Lean. The checker
(~8k lines), the parser (~2k lines) and the rule lemmas are all outside it,
because they are what the theorem is about rather than what it assumes.

## Known gaps

- Well-foundedness of Eunoia programs is not established, so smt-meta can
  report spurious unsoundness (Stage 7a).
- `eo::typeof` approximates rather than reproduces Eunoia's internal type
  system (Stage 5).
- The `:chainable` and assoc desugarings are mirrored in three places — the
  cvc5 API, the CPC signature, and the ethos parser — with nothing checking
  that the three agree (Stages 2 and 4).
- Mixed arithmetic is eliminated silently on the way into proof assumptions
  (Stage 3).
- How cvc5's global variable semantics relates to SMT-LIB's is unresolved
  (Stage 1).

## Future directions

- Fuzz ethos to confirm it stays synchronized with the desugaring semantics.
- An Isabelle backend, and possibly Agda or Dedukti backends.
- Parametric bitvectors in cvc5, to discharge the generated VCs.
- Logos as a reimplementation of ethos whose native language is desugared
  `*.eo`, formally verified so as to absorb some stages of this pipeline.
- Telos: an SMT solver API running cvc5 to the proof API to ethos or Logos.
- Alethe to Eunoia.

## Appendix: component sizes

Counts are code lines, excluding blank and comment lines. They are indicative
rather than exact, and go stale; refresh them with:

```bash
cloc --force-lang=Lisp,eo --force-lang=Lisp,smt2 <files>
```

A count for a C++ component is its implementation plus its header. Measured
2026-08-26.

### Shared infrastructure

| Component | LOC |
| --- | --- |
| ethos core, `src/` | 10,261 C++ |
| `src/plugin.h`, the callback interface | 64 C++ |
| `plugins/std_plugin`, `meta_reduce_plugin`, `utils` | 782 C++ |
| `plugins/main_eoc.cpp` | 206 C++ |
| `tools/eoc/driver.py` | 874 Python |

### Eunoia to Lean

| Component | LOC |
| --- | --- |
| `desugar.{h,cpp}` | 1,279 C++ |
| `desugar_checker.{h,cpp}` | 153 C++ |
| `model_smt.{h,cpp}` | 227 C++ |
| `defs_reader.{h,cpp}` | 447 C++ |
| `linear_patterns.{h,cpp}` | 176 C++ |
| `lean_meta_reduce.{h,cpp}` | 1,815 C++ |
| shared infrastructure | 782 C++ |
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

### Eunoia to SMT-LIB and SyGuS

The desugar and model-smt rows above are shared; this backend adds:

| Component | LOC |
| --- | --- |
| `smt_meta_reduce.{h,cpp}` | 945 C++ |
| `smt_meta_sygus.{h,cpp}` | 497 C++ |
| `smt_meta/utils.{h,cpp}` | 62 C++ |
| `trim_defs.{h,cpp}` | 756 C++ |
| `smt_meta.smt2` template | 293 SMT2 |

### Generated Logos

Sizes of the Lean package compiled from `Cpc.eo` with the CPC exclusions
applied. Reproducing these needs a full CPC run against a cvc5 checkout, so
treat them as a snapshot rather than a current measurement.

| Module | LOC | In TCB |
| --- | --- | --- |
| `SmtEval.lean`, evaluation utilities | 140 | yes |
| `LogosTerm.lean`, term datatype | 248 | yes |
| `SmtModel*.lean`, `SmtValueOrder.lean`, model semantics | 1,925 | yes |
| `Spec.lean`, Eunoia to SMT correspondence | 380 | yes |
| `Logos.lean`, the checker | 8,219 | no |
| `Parser.lean`, proof parser configuration | 2,004 | no |
| `RuleLemmas.lean`, rule lemma statements | 3,607 | no |
| `Rules/*.lean`, 591 per-rule files | 10,638 | no |

Trusted computing base: 140 + 248 + 1,925 + 380 = 2,693 lines of Lean.
