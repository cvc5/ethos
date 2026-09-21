# Compiler design and open questions

This page describes the compiler's configuration boundary and the work it
still leaves to a calculus author. The [driver](../README.md) explains how to
run it, eunoia's [`.eos` reference](https://github.com/ajreynol/eunoia/blob/main/tools/sapheneia/docs/eos.md)
defines the configuration language, and [proof-pipeline.md](proof-pipeline.md)
places it beside proof checking.
These are design questions, not commitments to change the language.

## Inputs and feedback

A model compilation takes an Eunoia signature and an explicit `--semantics`
file. `--smt-semantics` selects the target semantics; the default is
`tools/eoc/semantics/smt.eos`. Input paths resolve against the invoking shell's
working directory. There is no `EOC_SEMANTICS` environment variable.

The input must provide a meaning for each symbol that reaches the model stage,
apart from the stage's internal symbols. Unsupported symbols, methods and
rules can be excluded explicitly. Recursive programs that Lean cannot prove
terminating structurally need a `:lean` clause. N-ary operators with a
non-ground nil need the predicates described below.

`sem_compile.py` checks names, arities, binding and block dependencies.
`--check` additionally compares the generated files with their configuration.
Neither establishes that a case models SMT-LIB correctly. The feedback loop is:

```text
.eos -> sem_compile.py -> desugar -> trim-defs/model-smt
     -> smt-meta/lean-meta -> cvc5/Lean
```

The driver uses cvc5 for syntax checks of SMT-LIB and SyGuS output. It does not
build the generated Lean package. A successful compilation is not a proof of
soundness; the chosen model, translation and discharged obligations determine
what a result establishes.

## Configuration and templates

The configuration describes theory symbols and the constructors, programs and
natives used to interpret them. Templates describe the embedding and stage
structure. The implementation is shared between these files:

| File | Responsibility |
| --- | --- |
| [`sem_lang.py`](../compiler/sem_lang.py) | Read forms and macros, bind names and cast terms between levels. |
| [`sem_target.py`](../compiler/sem_target.py) | Shapes of generated programs, parameters and aggregate cases. |
| [`sem_compile.py`](../compiler/sem_compile.py) | Select sets, render files and check dependencies. |
| [`model_smt.eos`](../../../plugins/model_smt/model_smt.eos) | Model aggregate names, template markers and constructor families. |
| [`desugar.eos`](../../../plugins/desugar/desugar.eos) | Programs supplied to the desugar stage. |
| [`model_smt.eo`](../../../plugins/model_smt/model_smt.eo) | SMT term/type/value embedding and aggregate templates. |
| [`eo_desugar.eo`](../../../plugins/desugar/eo_desugar.eo) | Eunoia embedding and desugared list operations. |

The model stage reads aggregate metadata from the generated signatures rather
than enumerating theory symbols in C++. Adding an aggregate still needs its
shape in `sem_target.py` and a matching declaration and template marker.
The [configuration reference](https://github.com/ajreynol/eunoia/blob/main/tools/sapheneia/docs/eos.md#5-the-shape-of-what-is-written)
describes that contract. Tables here are explanatory copies, not mechanically
compared with that implementation.

The target is specifically an SMT-LIB model with separate term, type and value
languages. Maps represent arrays and sets; sequences represent strings.
Function application and binding have dedicated embedding behavior. A second
calculus can reuse this target, but a different semantic target can require
changes to the templates, shapes and native layers.

## Non-ground nil predicates

`$eo_is_list_nil` supports the desugared list operations. Its intended meaning
is `(eo::eq (eo::nil f (eo::typeof x)) x)`. A ground nil can be tested directly.
For a nil that depends on the type, the input configuration supplies a
predicate, for example:

```lisp
(define-symbol str.++ (s t)
  :is-list-nil (seq.empty T) true
  :is-list-nil s             (eo::eq s ""))
```

`plugins/desugar/desugar.eos` determines that this compiles to
`$eo_is_list_nil_str.++` in `tools/eoc/out/user_desugar.eo`.
`inline_called_blocks` in the driver inserts the predicates the desugared
signature calls, before their uses. They are not model-stage aggregate cases.

Two checks remain open: whether every operator needing such a predicate has
one, and whether each supplied predicate agrees with the intended meaning.
The driver selects available definitions but does not compare a required set
against a provided set. A missing definition can therefore surface only when
a later stage reparses the output. An incorrect predicate can silently alter
list behavior. The local n-ary regression exercises a supplied predicate, not
its equivalence for every term.

Using the generated `$eo_typeof` directly is not an exact replacement: that
program approximates Ethos's type system by generating cases for particular
partial applications. The design question is how to discharge the predicate
obligation without treating that approximation as the original type system.

## Other boundaries that need care

- **Shared generated files.** Sets compile by role to fixed files under
  `tools/eoc/out/`; the plugins also share files under their build directory.
  Different `--final-out-dir` values alone do not isolate concurrent runs.
- **Exclusions.** Names are literal, with no dependency closure or check that
  every excluded name exists. Related declarations must be excluded together.
- **Dependency metadata.** The configuration writes `$eoc-depends` and
  `$eoc-exclude` comments; the driver turns them into stage directives. Changes
  must agree with both readers.
- **Native coverage.** Some operations are supplied by the backend language,
  some by a native layer, and some are deliberately opaque. There is no full
  check that every operation a run reaches has an implementation in its target.
- **Termination.** `:lean` carries Lean text, whose proof is checked downstream.
- **Helper families.** Aggregate names are configuration, but the helper's
  argument/result shape is Python. [eos-todo.md](eos-todo.md) describes that
  remaining split.

## Possible directions

Check nil-predicate coverage before invoking a backend, then provide obligations
for the meaning of those predicates. Make native coverage explicit per backend.
A per-symbol explanation command could shorten the configuration feedback loop.
An exclusion check should distinguish omitted names from missing dependencies.
None of these is implemented by merely running `--check`.

Allowing a calculus to name arbitrary native operations would be a separate
language design decision. Naming a backend operation supplies neither its type
nor its meaning to Ethos, and would require a clear account of both before any
soundness claim could rely on it.
