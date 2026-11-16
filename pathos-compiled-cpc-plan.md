# A compiled CPC checker in pathos, verified against logos

Status: proposal. Written 2026-11-16 against pathos `f77aff7`, logos `512983a8`,
ethos `c077a562`.

## Summary

Add an eoc output target, `rust-meta`, that prints the same desugared program
that `lean-meta` prints, as Rust. Its output is the whole Logos checker in Rust:
the CPC term type, the rule programs, and the Eunoia checking loop (`CState`,
`__eo_cmd_step_proven`, `__eo_invoke_cmd_list`) together with the translation
side conditions. pathos supplies the parser, elaboration and the hash-consed
term store, and ships the result as a separate checker, `pathos-cpc`.

Because each generated Rust function has exactly one counterpart in
`Cpc/Logos.lean`, the Rust can be verified against logos one function at a
time. The plan is to extract the Rust to Lean with Charon and Aeneas, prove
that each Rust function refines its Lean counterpart, and compose the result
with logos's existing soundness theorem.

## Background

**pathos** reimplements Ethos's interpreter in Rust. It reads `Cpc.eo`, and
`check_step` (`crates/pathos-check/src/step.rs`) runs each rule's program by
matching its cases one at a time (`evaluate_program_internal` in `eval.rs`).
Its signature snapshots, like Ethos's `cpp_compiler` plugin, only save the
parsed state, so rules still run through the interpreter. pathos also has an
evaluation hook (`EvalPlugin`) for compiled programs, which no stage uses.

**logos** is already a compiled CPC. The eoc pipeline
`trim-defs → desugar → lean-meta` works like this:

- `desugar` turns CPC, together with Eunoia's own checking
  (`plugins/desugar/eo_desugar_checker.eo`: typing, the proof state, step and
  command invocation), into first-order equations over a single `Term` type
  with an explicit `Stuck` constructor.
- `lean-meta` mostly just prints those equations. The result is
  `Cpc/Logos.lean`, about 10.8k lines, all of it total (17 functions use
  `termination_by` or `decreasing_by`; none are `partial`).
- The soundness theorems (`correct___eo_is_refutation`,
  `correct___logos_state_is_refutation`, `correct___logos_check_proof`) are
  stated about those functions.

## Decision A: compile, and compile the whole checker

### Why compiled code rather than the interpreter

1. **The interpreter cannot be connected to logos at reasonable cost.** That
   would need a formal semantics of Eunoia (matching, `eo::requires`, stuck
   propagation, list operators, attributes), a proof that pathos's interpreter
   implements it, and a proof that `desugar` preserves it. None of these
   exist, and logos was designed so that it does not need them: its theorems
   are about the desugared functions, not about Eunoia.
2. **Compiled output matches `Logos.lean` function by function.** Both targets
   print the same desugared equations, so verifying the Rust comes down to one
   mechanical simulation lemma per function. The stage can generate these
   lemmas itself, as `lean-meta` already generates the rule lemmas
   (`plugins/lean_meta/lean_meta_rule_lemmas.lean`).
3. **Speed is a bonus.** Snapshots already cover the time spent loading
   `Cpc.eo`. Compiling the case matching removes the interpretive overhead on
   every step. pathos's brief had ruled out this optimisation for the
   interpreter because it could change behaviour.

### Why the whole checker, not just the rule programs

The `EvalPlugin` route, which plugs compiled programs into the interpreter's
`check_step`, would leave the step logic unverified: building the premise
list, `:assumption` and `step-pop`, and typing the arguments. logos's
soundness chain runs through the state and command invocation, so the
generated Rust has to include these too:

- the CPC term type, mirroring `Cpc/LogosTerm.lean`;
- every desugared function, including the `__eo_*` checking functions;
- `CState`, `CRule`, `CArgList`, `CIndexList` and `CCmd`, with
  `__eo_invoke_cmd_list` and the check that the final state is a refutation;
- the side conditions in `Cpc/TranslationChecks.lean` that decide between
  `correct` and `incomplete`. Those that are not generated today would need a
  Rust counterpart, written by hand or generated.

### Design points

- **A term type specific to CPC.** Generate a `TermData` enum that mirrors
  logos's `Term` exactly: `UOp(UserOp)`, `UOp1`/`UOp2`/`UOp3`, `Apply`,
  `Boolean`, `Numeral`, `Rational`, `String`, `Binary`, `Stuck`, `Var`, the
  datatype constructors, `USort` and `UConst`. Intern it in an arena with
  `u32` handles, like pathos's store (decision 1 of the pathos brief). logos
  gives each CPC symbol its own constructor, where pathos uses generic kinds
  and symbol names. Keeping the Rust and Lean types identical makes the
  relation between them close to the identity, which keeps the proofs simple.
- **Reuse pathos's front end.** pathos's parser and elaboration stay as they
  are. A generated translator maps pathos terms to `TermData`, in the role
  that `Cpc/Parser.lean` plays for logos.
- **A small, fixed term API.** The generated code uses only `view` (a handle
  to its shape), the `mk_*` constructors and the native operations. This API
  is where the proof meets the store, so it should stay narrow.
- **It follows logos, not Ethos.** Verdicts should agree with Ethos on the
  corpus. Error messages and corner cases (stuck terms, typing) will not match
  Ethos byte for byte. The interpreter remains pathos's default, the
  Ethos-compatible checker, and serves as a test oracle. The compiled checker
  is a separate binary or mode, `pathos-cpc`, reporting
  `correct`/`incorrect`/`incomplete` as `logos` does.
- **Native operations must match Lean's definitions, not GMP's.** This covers
  every `native_*` function in `Logos.lean`: integer division and modulo,
  `native_int_log`, the string operations, and the recursions that run on fuel
  such as `impl_native_str_indexof_rec`. The fuel has to be the same.
  pathos currently matches GMP, which is a different target.
- **Recursion depth.** pathos's brief requires iterative traversals. Generated
  code is naturally recursive, and recursive code is much easier to verify.
  Keep it recursive and run the checker on a thread with a large explicit
  stack. A stack overflow aborts the run. That counts as a rejection, never as
  an unsound acceptance.

## Decision B: verify with Aeneas against logos's theorems

Aeneas (Charon extracts the Rust, Aeneas translates it to Lean 4) is the only
mainstream Rust verifier whose output lands in Lean. The proof can therefore
reuse logos's existing theorems instead of restating the specification in
Verus or Creusot.

- pathos forbids `unsafe`, which Aeneas requires.
- Aeneas treats recursive functions as possibly non-terminating, so the result
  is partial correctness: if the Rust checker returns `correct`, the Lean
  checker returns `correct` on the same commands. Soundness needs no more.
- `HashMap`, which the store uses for interning, and `malachite` are probably
  beyond Aeneas. Give them opaque models with stated specifications.

### The proof in four layers

1. **Store model.** Define `denote : Store → Handle → Option Term` and prove:
   - `mk_*` and `view` behave as Lean's constructors and pattern matching;
   - operations only grow the store, so existing handles keep their meaning;
   - two handles are equal exactly when their terms are equal (hash-consing),
     so comparing handles decides `Term` equality.

   State these as axioms at first and prove them against pathos-term later.
2. **Per-function refinement, generated by `rust-meta`.** For each generated
   function `f`:

   ```
   denote s xs = some as →
   f_rs s xs = ok (s', r) →
   extends s s' ∧ denote s' r = some (Eo.f as)
   ```

   Both sides come from the same desugared equation, so one uniform tactic
   (unfold, then a case split that follows the pattern compilation) should
   prove them all.
3. **Top-level theorem.** Compose the refinement of `__eo_invoke_cmd_list`
   and the refutation check with `correct___logos_state_is_refutation`
   (`Cpc/Native/Correct.lean`). That theorem is stated about `assums` and
   `cmds`, not about the proof text, so the Rust parser stays out of the proof.
4. **Trusted base.** What remains trusted:
   - pathos's parser and elaboration, and the generated translator to
     `TermData`, in the role `Parser.lean` plays for logos;
   - rustc, Charon and Aeneas;
   - the store and native-operation axioms, until they are proven;
   - the Lean kernel and logos's specification (`Cpc/SmtModel.lean`,
     `Cpc/SmtTranslate.lean`, `Cpc/Spec.lean`).

## Plan

| Phase | Work | Where |
|---|---|---|
| 0 | Design the term API and the generated `TermData` enum from `LogosTerm.lean`; decide how `Stuck`, the native operations and fuel are represented | this document |
| 1 | Add the `rust-meta` stage after `desugar`: a C++ plugin in `plugins/rust_meta` with templates like `lean_meta_*.lean`, and `driver.py rust`. Port it to `pathos-eoc` byte for byte, under pathos's `eoc` gate | ethos, pathos |
| 2 | Build `pathos-cpc`: pathos's parser, then the generated translator to `CCmdList`, then the generated `__eo_invoke_cmd_list` and translation checks, giving `correct`/`incorrect`/`incomplete` | pathos |
| 3 | Differential testing before any proofs, on the 400 cvc5 proofs, the 43 large ones and logos's regressions: verdicts against `logos` and Ethos, and pathos's translated `CCmdList` against what `Parser.lean` produces. This is the baseline and also checks the parser | pathos harness |
| 4 | Run Charon and Aeneas on the generated crate. Add the store and native axioms. Have `rust-meta` also emit the refinement lemmas and the top-level theorem | `logos/verification/` |
| 5 | Prove the axioms: the store model against pathos-term, then the native operations, starting with the integer and rational ones | logos |

The refinement theorems and the Aeneas project belong in
`logos/verification/`, since logos owns the CPC semantics. The generator
belongs in ethos, with its port in pathos.

### First experiment, before phase 4

Write a few rules by hand in Rust (`symm`, `trans`, `contra`) over a small
hash-consed store, and run Charon and Aeneas on them. This shows quickly
whether Aeneas copes with:

- threading `&mut Store` through every call, and
- mutual recursion at the size of `Logos.lean`.

These are the two places most likely to cause trouble.

## Open questions

- Should `pathos-cpc` be a separate binary or a mode of `pathos`?
- Are the translation side conditions generated today, or written by hand in
  logos? This decides whether `rust-meta` can emit them or they need a
  hand-written Rust version.
- Should the store's specification be proven against pathos-term's code
  through Aeneas, or should the generated crate carry its own smaller store
  that is easier to verify?
- How far pathos's elaboration and `Parser.lean` agree on n-ary operators and
  overloads. Phase 3 measures this; a disagreement changes the formula the
  theorem talks about.
