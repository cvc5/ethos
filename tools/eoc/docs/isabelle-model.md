# Adding the SMT model to Isabelle

Investigation of the boundary between Isabelle's executable checker and the
model semantics used to prove its soundness. Model generation is not yet
implemented in `isabelle-meta`; the architecture below is a proposal.

## What can remain unchanged

Adding model semantics does not require changing `check_refutation`, the rule
programs it calls, their fuel arguments, or the parser. The new definitions
belong to theories that import the checker. The checker must not import them.

This boundary was tested on both the `contra` fragment and the entire local
CPC signature, using the development CPC semantics:

1. Desugar the signature with the existing Isabelle dependency roots.
2. Generate the existing checker after removing the model inclusion marker.
3. Independently run `model-smt` on the same desugared signature and parse its
   output successfully.
4. Trim that output to the existing checker roots and generate Isabelle again.
5. Compare the emitted files as bytes.

All six artifacts were identical: checker theory, existing abstract spec,
syntax table, parser, s-expression reader, and export-binding script. This
establishes that the model stage itself can be inserted without changing the
checker output, provided the two dependency sets remain separate. It does
not test an Isabelle translation of the model.

The repeatable regression is:

```sh
python3 tools/eoc/test/isabelle_model_boundary.py \
  ~/cvc5-ajr/proofs/eo/cpc/Cpc.eo \
  --semantics tools/eoc/semantics/development-cpc.eos
```

An additional local Isabelle2025-2 probe imported the generated `contra`
checker and defined a small, handwritten semantic evaluator by structural
primitive recursion. Its quantifiers range over all natural numbers and its
choice operator uses `SOME`. Isabelle proved the universal-identity,
existential-zero, and choice-zero examples without axioms or `sorry`.
Exporting `check_refutation` before and after adding those definitions gave
identical SML (154,095 bytes). This is a test of the proposed separation,
not a generated or complete SMT model. The local probe lives under
`scratch/isabelle-model-investigation/hol/` and is not a committed fixture.

## Two generation branches

The current driver explicitly removes `include model_smt` and trims to
`ISABELLE_DEPS`. Keep that checker generation path and add a model branch
from the original desugared input:

```text
                       checker dependencies -> Checker + Runtime parser
                      /
signature -> desugar -+
                      \
                       model-smt -> model dependencies -> model theories
```

The proof branch needs the SMT term, type and value datatypes; maps,
sequences, regular languages and datatype declarations; the model record;
the evaluator and typing/default/canonical-value helpers; and
`$eo_to_smt` / `$eo_to_smt_type` with their translation helpers.

The present backend emits every collected datatype and program into the
checker theory. Feeding the combined input to that emitter would change the
checker artifact and encounter unsupported model types. Add a separate
emission path rather than simply enlarging `ISABELLE_DEPS`.

That path should reuse the checker's allocated names through an explicit
binding map. Constructor names, collision suffixes, enum chunks and mutual
program identifiers are allocated by the checker emitter. A second pass must
reference those definitions, not allocate independent copies of them. Model
definitions also need their own namespace or identifier allocation domain.

A possible generated proof package is:

| Theory | Contents |
| --- | --- |
| `Cpc_SmtDefs` | SMT datatypes and native support |
| `Cpc_SmtModel` | Model, evaluation, model well-formedness, satisfaction |
| `Cpc_Interpretation` | EO-to-SMT translation over the existing checker `Term` |
| `Cpc_ModelSpec` | Rule and checker contracts using that interpretation |

Place these in a separate generated session with `Cpc` as a parent, for
example `Cpc/Model/`. The native runtime can retain its existing `Cpc` parent
and checker imports. Iogos's soundness session would depend on the new model
session. Adding model imports to the current `Cpc_Spec` instead would also
make the runtime's parent session build the model; that would preserve the
checker definition but unnecessarily couple the build paths.

`install_iogos` already supplies the CPC semantics configuration. It can
request and install the model package along with the checker, publishing only
after both branches succeed. Checker-only generation should remain possible
for signatures that do not supply model semantics.

## Logical semantics and checker fuel

The checker budget bounds EO program execution. Model truth should not depend
on that budget. In particular, an exhausted computation is not evidence that
an existential statement is false or a universal statement is true.

The main SMT evaluator can use structural recursion on its term argument,
returning a function of the model. Recursive occurrences under quantifiers
then evaluate the strictly smaller body in an updated model. The local HOL
probe confirms that this form supports logical quantification and choice
without adding fuel to the semantic interface.

The full model still needs termination work. The existing Lean configuration
contains measures for mutually recursive datatype defaults and boundedness
helpers, as well as the structural evaluator. Those Lean proof snippets are
not Isabelle proofs. Port them to proof-side Isabelle definitions and
termination arguments. Do not use termination axioms or reinterpret fuel
exhaustion as a semantic value. A fuel-based helper could be reused through a
logical wrapper only after proving the existence and uniqueness of its result.

Model-native dependencies also include callbacks that ordinary EO call-graph
traversal cannot see. For example, `eval_exists`, `eval_forall` and
`eval_choice` call the evaluator, type-of-value and canonical-value predicates;
`inhabited_type` uses type defaults. The model emitter must retain and order
those dependencies explicitly, as the Lean templates do.

The native port includes model lookup/update, type and value equality and
ordering, quantification and choice, and the reached string, sequence and
regular-language operations. It is more than adding cases to `type()`.

## The proof obligations must change

The current `obligation_* valid fuel ...` predicates say that a successful,
non-stuck result satisfies an arbitrary `valid` predicate. They do not express
the semantic truth of the premises, and `checker_sound_for` separately takes
an arbitrary unsatisfiability predicate. Supplying a concrete interpretation
alone does not connect these definitions into a checker soundness theorem.

The new contracts should state, schematically:

```text
well-formed model
  + translation/typing conditions on arguments and premises
  + premise truth in that model
  + rule execution at any checker fuel returns a non-stuck result
  -> truth of the translated result in that model
```

Rules that discharge assumptions need a scope-aware contract. Binder-sensitive
rules may require premise truth under suitable changes to variable bindings.
Logos's `StepRuleProperties`, `StepPopRuleProperties`, and checker invariants
provide useful reference interfaces; their proofs do not automatically port.

Proving that the generated command interpreter preserves the corresponding
state invariant is a further proof task. Generating the model does not itself
prove either the individual rule contracts or the checker theorem.

## Implementation order

1. Keep the checker/parser byte-identity regression. Introduce the independent
   model output path and explicit checker bindings.
2. Generate model datatypes, Boolean operations and EO interpretation from the
   actual `model-smt` output. Build them in HOL and prove a first ordinary rule
   contract against the unchanged checker.
3. Port the remaining reached natives and recursive helpers, including
   quantifiers, choice, datatype defaults and canonical values. Use Isabelle
   proofs for termination where structural recursion does not suffice.
4. Generate semantic rule contracts and expose them to Iogos's soundness
   session. Extend installation to the new generated session and preserve the
   current runtime build path.

The intended changes are therefore proof-side definitions, proof contracts,
proofs, and generation/session wiring. Checker definitions and acceptance
behavior can remain unchanged throughout this work.
