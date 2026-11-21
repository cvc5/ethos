# Rust meta backend

`rust-meta` is an **ethos-eoc plugin** that emits a standalone safe-Rust
checker for use by Pathos. It compiles the entire checking loop, including
rule programs, typing, assumptions, premise lookup, `step-pop`, command
invocation and the final closed-refutation test. It emits no proof parser.
The generated crate depends only on the same pinned Malachite packages as
Pathos, with the runtime copied into the artifact.

Generate a checker from a signature:

```sh
python3 tools/eoc/driver.py rust --build-dir build-eoc \
  --final-out-dir build-eoc/compiled tests/Booleans-rules.eo
cargo test --locked --manifest-path build-eoc/compiled/rust/Cargo.toml
```

For CPC with Logos's SMT translation and typing checks:

```sh
python3 tools/eoc/driver.py rust --build-dir build-eoc \
  --final-out-dir build-eoc/compiled-cpc \
  --semantics ../logos/install/defs/Cpc.eos \
  --smt-semantics ../logos/install/defs/smt.eos \
  ../logos/install/defs/Cpc.cached.eo
cargo build --locked --manifest-path build-eoc/compiled-cpc/rust/Cargo.toml
```

The generator needs the usual Ethos C++/CMake/GMP build environment.
Compiling the artifact needs Rust 1.99 or later. No Rust toolchain is needed
to build or run ethos-eoc itself. `--no-build` reuses an existing ethos-eoc.
The raw stage is also available as
`ethos-eoc --plugin.rust-meta <structural-desugar-or-model-smt-output.eo>`;
`--no-parser` is accepted and is redundant for this backend.

The driver uses structural desugaring for the term embedding, signature
metadata and checking loop. Builtin operators call the Rust runtime
directly; their desugared EO implementations are neither compiled nor
interpreted. With `--semantics`, model-smt also supplies the static SMT
translation and typing functions. No model evaluator is emitted.

## Using the artifact in Pathos

Add the emitted crate as a path dependency, or copy its sources into the
desired Pathos crate. It has its own arena and runtime; it does not depend
on Pathos's interpreter or link against C/C++.

The parser/elaborator adapter constructs terms and commands through:

- `Store::literal`, `boolean`, `numeral` and `apply` for object terms;
- `Store::raw` for native constructor fields, including premise indices,
  datatype indices and uninterpreted-symbol identifiers;
- `Store::named(source_name, fields)` or
  `Store::construct(Constructor, fields)` for generated constructors.

`Constructor::from_name` and `constructors.tsv` preserve EO names, including
overload identities. `functions.tsv` maps source programs to Rust functions,
their Lean counterparts and the module each is in (see "Verification
boundary"). `caches.tsv` records which functions are cached
and their artifact-local program IDs. Identifiers escape punctuation and
underscores injectively, so source names cannot collide with Rust keywords
or each other.

Beside the crate the stage writes Lean about it, for the proofs of the
pathos repository (`proofs/` there; the files name the modules they import
by the placeholders `$CHECKER$`, `$CALC$` and `$CASES$`, which pathos
fills in):

- `proofs.lean`: for each program, the proof that its Rust functions, as
  Aeneas translates them, compute what logos's function of the same name
  does. The emitter records a line of proof with each line of Rust it
  writes, in the tactics of pathos's `PathosProofs/Tactic.lean`: a theorem
  for each case against the case's function in lean-meta's
  `lean_meta_case_defs_gen.lean`, one for the body (the tests for the
  stuck term, then the cases in order; for a tail-call loop, a round of it
  and the induction over the loop), and one for the program between
  `enter` and `leave`, with its cache. A lemma per program says that
  logos's function is the first case that answers; it is proved, by
  unfolding both sides, never assumed. Calls of programs use what is proved
  of them at a smaller number of calls that may still be entered, and one
  induction on that number closes all of them together.
- `proofs.tsv`: for each program, whether it has a proof and, if not, the
  first thing in it that the emitter has no line of proof for yet.
- `cache_sem.lean`: for each cached program with a proof, what an entry of
  its cache says; the store's invariant in the proofs is stated with it.

The Rust is the same with or without these files.

The public checking entry points take the generated `CArgList` and
`CCmdList` representations as arena handles:

```rust,ignore
let derivable: bool = store.check_refutation(assumptions, commands)?;
let verdict: Verdict = store.check_proof(assumptions, commands)?;
```

`check_refutation` checks derivability. `check_proof` returns `Correct`,
`Incorrect` or `Incomplete`, and includes Logos's assumption/command
translation checks. Without generated SMT translation it returns
`Incomplete` for an accepted refutation. CPC's 32 special argument masks
are recorded in `cpc_translation_masks.txt`, with the corresponding Logos
revision. Keep that table synchronized with `Cpc/TranslationChecks.lean`.

`Term` is a private `u32` handle local to one monotonically growing,
hash-consed `Store`. Generated constructor arities are checked. Object
literals and native fields are distinguished. Indexed user operators have
the same views as Logos's `UOp<n>` constructors. Handles and raw state must
not be transferred between arenas.

Bad shapes and resource exhaustion are `Result` errors. Calls, recursive
depth and arena size are bounded by `Limits`; tail calls become loops,
including command invocation. Checking runs on a 256 MiB scoped-thread stack,
with a default depth limit of 16,384 generated calls, budgeting 16 KiB of that
stack per call. Every case of a program is a function of its own, the cases
are tried in nested groups of four, and a case's body goes on in a further
function after twelve statements. A call of a program is therefore a short
chain of small frames (the program, a group function for each level of
nesting, the case and its continuations) rather than one frame with the
temporaries of every case, in unoptimized builds too. The depth limit
counts calls of programs, not these frames. The depth regressions check both
successful deep terms and recovery after exceeding the limit in debug and
release builds. Stack use still depends on the signature, compiler and
target; the limit is configurable, not a universal stack-size proof.

The assumption-list program is recognized by its two-case guarded-fold
shape and compiled to a loop. Guards are evaluated head to tail and saved
with their terms; pushes run tail to head, preserving premise indices,
failed guards and malformed-tail results. One budget tick replaces each
recursive call, without increasing recursive depth. The refinement target
is the original EO function; Logos's `invoke_assume_list_eq_fold` in
`Cpc/ApiChecks.lean` proves the corresponding fold equality for its API.

## Evaluation caches

All memoization lives in `Store`, behind the small interface implemented by
`runtime/cache.rs`. It uses `Vec` tables and explicit loops, with no closures
or `HashMap`. The arena's interner is written the same way, in `Store`
itself: each term's hash is kept beside its data, and an open-addressed
vector of handles with linear probing, at most half full and doubled when
it would be fuller, finds a term from its data. A search compares the
data it finds with the data it looks for, so the hash function
(`runtime/table.rs`) matters only for speed.

Each term handle has one type-cache row with separate EO and SMT slots for
`$eo_typeof` and `$smtx_typeof`. Keeping these slots separate prevents two
different typing functions from sharing a result, including on `Stuck`.
Program applications use an open-addressed table keyed by the generated
program ID and **all** argument handles, including environments and fuel.
Hash collisions are resolved by checking the full key.

The generator caches programs in recursive call-graph cycles, including
mutual recursion, when they have a term or embedded-datatype argument. It
excludes checking-state functions, macros and nonrecursive helpers. This
keeps lookup overhead off ordinary rule dispatch and small helper calls.
`caches.tsv` makes this selection inspectable. Tail-call loops keep their
original arguments as the cache key.

Only completed `Ok` results are stored; an `Ok(Stuck)` is a legitimate
result, while errors, exhausted budgets and unfinished calls are never
cached. The cache invariant is that each entry equals the pure function's
result on the decoded argument handles. Arena growth preserves that
invariant, so entries survive across proof checks. Program entries are
bounded by `Limits::terms`; reaching that bound stops new insertions without
changing evaluation. Type rows grow with the arena.

`Store::cache_stats()` exposes hits, misses and entry counts for measurement.
`set_caching(false)` bypasses reads and writes; `clear_caches()` clears
entries and resets statistics without changing terms. Cache hits still
consume a generated-function call from the evaluation budget. Memoization
can turn an otherwise budget-exhausting traversal into a successful check;
successful results retain the same meaning.

## Verification boundary

This is an executable backend, **not a completed Rust verification**. The
function manifest supports a subsequent Charon/Aeneas refinement project in
Logos. No generated theorem asserts that this Rust is already sound.

What holds now is that Charon and Aeneas translate the whole checker to
Lean without an error, and that for CPC each module's Lean file compiles.
The generator and the runtime are written in
the subset of Rust the two accept, and the generated functions are in
modules `generated::part<k>` (`src/generated_part<k>.rs`) made from the
call graph: functions that call each other are in one module, and a module
calls only itself, earlier modules and the runtime. The runtime's list
operators and checking entry points, which call generated functions, are
placed in that graph with them. One module can so be translated at a time,
with the others opaque; their Lean files have not been put together into
one development. Aeneas needs two options:

- `-loops-to-rec`, because a loop written with its `loop` combinator does
  not compile in Lean when the function it is in is called again from
  inside the loop;
- `-max-heartbeats` above its default, for large groups of functions that
  call each other, which Lean elaborates as one definition.

Two parts of the runtime are not translated, and their functions are
axioms of the Lean: `num.rs`, the integers and rationals over Malachite;
and of `front.rs`, which holds what works on text for the program around
the checker, the one pure function the checking code calls
(`constant_name`). Literals and numerals are built as values.

The intended store relation maps each handle to its Logos term or native
field. Its obligations are constructor/view correctness, monotone extension
and structural equality iff handle equality. The arena's tagged sum also
holds checker states and native fields; the relation is indexed by the
generated type. Per-function proofs then relate the compiled cases to the
functions named in the manifest. Tail-call loops need the corresponding
iteration invariant. Translation masks and runtime operations need their
own refinement proofs. Cache refinement additionally requires the entry
invariant above; the table's hash layout is irrelevant to decoded results.

Literal and list operations follow Ethos/Pathos, with explicit stuck results,
lazy conditionals, ordered nonlinear matching and no fall-through after a
matched case's failed requirement. Rational/decimal and binary/hexadecimal
values are canonicalized to Logos's constructors. Term comparison uses
Logos's structural constructor/field order, including numerator/denominator
order for rationals, rather than Ethos's unspecified hash order. `eo::hash`
is rejected at generation because Logos has no specification for it.

Ethos's partial operations and Logos's totalized natives have different
domains, notably exponent and width bounds. Refinement must establish the
required domain conditions or account for rejection; matching the source
program names alone is insufficient. Unsupported native operations fail
with an error, never an accepting default. The parser and its translation
to this representation remain outside the proof, as requested.

Five files of the runtime (`num.rs`, `lit.rs`, `kind.rs`, `bitvec.rs`,
`eostring.rs`) come from `crates/pathos-term/src` at Pathos
`acae6aa1e2d4525c33c11c6aa74c725566be1ff5`. `eostring.rs` is a byte-for-byte
copy. The others are that code without what the compiled checker does not
use (the kinds of symbols and compound terms and the flat `Kind`, the
writing and reading of snapshots, a few functions on numbers), rewritten
in the subset of Rust that the verification tools translate; the header
of each says what it holds. The other runtime files (`cache.rs`,
`table.rs`, `native.rs`, `front.rs` and the `.in` templates) are this
backend's own. The BSD license is in `LICENSE.pathos`.
The artifact includes `Cargo.lock` and the Pathos
dependency audit in `DEPENDENCIES.md`. Its own Rust forbids `unsafe`; the
audited transitive dependencies retain Pathos's existing safety boundary.

## Regression checks

```sh
python3 plugins/rust_meta/test/run.py --build-dir build-eoc

# Optional: compile and check the full CPC from a local Logos checkout.
python3 plugins/rust_meta/test/run.py --build-dir build-eoc \
  --cpc ../logos/install/defs/Cpc.cached.eo --debug-only
```

This generates an independent crate, runs Rustfmt and Clippy with warnings
as errors, and runs debug and release tests. (The runtime allows a few
Clippy lints by name, those that ask for an idiom the verification tools
do not translate.) Coverage includes a complete
refutation, incorrect premises, assumption discharge, open scopes,
ill-typed assumptions, builtin lists and arithmetic, nonlinear matching,
lazy recursion, tail-call argument swapping, long command lists and resource
limits. All six builtin recognizers are checked on `Stuck` and literal/variable
inputs. The existing driver tests and compiler regressions still apply.
Depth regressions include a 15,000-level right-nested `or`, a term beyond the
default depth budget, and 120,000 assumptions with an explicit depth limit
of 128. Fold regressions check failed guards, initial states, input order
and malformed tails.
Cache regressions include a 40-level shared DAG (exponential as a tree),
mutual recursion, distinct program IDs and environments, collisions and
rehashing, arena growth, bounded insertion and cleanup after errors. They
also compare cached and uncached proof results. The shared DAG completes
within a 1,000-call budget with caching and exhausts that budget without it.
The CPC run also compares the mask table with that checkout's
`Cpc/TranslationChecks.lean` when the file is available, and checks the
`arith_poly_norm` refutation of `(not (= x x))` for a real constant with
caching enabled and disabled.
