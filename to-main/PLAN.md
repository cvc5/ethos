# Sending `ethosEoc3` to `main` — three PRs

`origin/main` (`8709609e`) **is** the merge base, so nothing needs rebasing:
the branch is strictly ahead. What has to be managed is review size — 1342
commits, **77 files, +10044 / -3267** — and keeping CI green at each landing.

Three patches, applied in order, reproduce `ethosEoc3` from `origin/main`
**byte for byte** (verified: same tree object, `9d788e12`).

| PR | Patch | Scope | Size |
| --- | --- | --- | --- |
| **1** | `1-eoc-engine.patch` | the compiler and the four stages | 59 files, +6903 / -3014 |
| **2** | `2-driver-and-gate.patch` | `driver.py`, the `cpc/` wrappers, the regression and the CI gates | 14 files, +1724 / -253 |
| **3** | `3-docs.patch` | `proof_pipeline.md`, `docs/`, root README | 4 files, +1417 |

```
PR 1 ──→ PR 2
  └────────────→ PR 3        (3 needs nothing from 2; it only *describes* it)
```

**Sequential:** 1 → 2. PR 2 is the tool that drives what PR 1 adds, and the
regression that pins it.
**Parallel:** PR 3 can be opened and reviewed alongside either. Land it after
PR 2 so it does not document something that is not there yet — but it blocks
nothing and nothing blocks it.

---

## Verified, not assumed

Each of these was run, not reasoned about:

- the three patches partition the delta — all 77 files, none twice, none
  missed — and applied in order onto a clean `origin/main` worktree they
  reconstruct `ethosEoc3` exactly;
- **PR 1 alone** builds under CI conditions (`cmake -S plugins`, Debug,
  `-Werror`) and passes `ethos-eoc tests/simple.eo`;
- **PR 1 + PR 2** passes every step of the workflow PR 2 installs:
  `sem_compile.py --check` clean, and `regress.py --require-cvc5` reporting
  *21 files, all as checked in* with cvc5 reading back the `.smt2` and `.sy`.

So there is no landing order in which CI is red, and no step where you have to
guess.

---

## Why PR 1 is one PR and not five

It is large, and it cannot be usefully cut. Three couplings, each found by
trying it:

1. **The `MetaKind` enum.** `plugins/utils.h` removes `SMT_BUILTIN_DATATYPE`;
   `lean_meta_reduce.cpp` and `smt_meta_reduce.cpp` still name it. Splitting
   the shared infrastructure from the backends fails to compile.
2. **`dropResourceNotes`.** `std_plugin.cpp` calls it and `utils.cpp` defines
   it, so those cannot be separated either.
3. **The build runs the compiler.** `plugins/CMakeLists.txt` on `main` already
   carries

   ```cmake
   add_custom_target(eoc-semantics
     COMMAND ${Python3_EXECUTABLE} "${ETHOS_SOURCE_DIR}/tools/eoc/sem_compile.py" ...)
   add_dependencies(ethos-eoc eoc-semantics)
   ```

   so `sem_compile.py` runs on every build. `main`'s compiler cannot read the
   branch's `.eos` sets and the branch's compiler cannot read `main`'s, so the
   compiler and every `.eos` move together — which is most of `plugins/`.

If PR 1 still needs to be broken up for review, the one edit that buys a
separate infrastructure PR is to keep `SMT_BUILTIN_DATATYPE` in the enum and
delete it later; coupling (2) is internal to that PR either way, and (3) fixes
the rest of the boundary.

---

## Applying

`git apply` writes files but stages nothing, so new files are left untracked.
`git add -u` picks up every modification; the new files are listed per PR
below.

### PR 1 — the eoc engine

```bash
git checkout -b eoc-engine origin/main
git apply to-main/1-eoc-engine.patch
git add -u
git add plugins/desugar/desugar.eos plugins/desugar/natives.eos \
        plugins/eo_meta/README.md plugins/eo_meta/eo.eos \
        plugins/lean_meta/lean.eos plugins/model_smt/model_smt.eos \
        plugins/native_layer.cpp plugins/native_layer.h \
        plugins/smt_meta/smt-vc.eos tools/eoc/report.py \
        smtlibTests/logos-tests/
# what CI will do:
cmake -S plugins -B build-eoc -DCMAKE_BUILD_TYPE=Debug -DCMAKE_CXX_FLAGS=-Werror
cmake --build build-eoc --target ethos-eoc -j8 && ./build-eoc/ethos-eoc tests/simple.eo
```

Contents: the shared plugin infrastructure (`utils`, `std_plugin`,
`native_layer`, `meta_reduce_plugin`, `main_eoc`), the configuration compiler
(`sem_compile`, `sem_lang`, `sem_target`, `report`) with the sets under
`tools/eoc/semantics/`, all four stages (`desugar`, `model_smt`, `lean_meta`,
`smt_meta`, `eo_meta`) with their `.eos`, plus the `smtlibTests/logos-tests/`
inputs and `.gitignore`.

### PR 2 — driver, wrappers and the regression gate

```bash
git checkout -b eoc-driver eoc-engine     # or origin/main once PR 1 has landed
git apply to-main/2-driver-and-gate.patch
git add -u
git add tools/eoc/cpc/ tools/eoc/test/expected.txt tools/eoc/test/regress.py
# what CI will do, in addition to PR 1's steps:
python3 tools/eoc/sem_compile.py --check
python3 tools/eoc/test/regress.py --build-dir build-eoc --require-cvc5
```

The `cpc/` scripts are executable; the patch carries mode 755, so nothing
extra is needed.

This PR is what switches the pipeline checks on in `.github/workflows/main.yml`
— including downloading a pinned cvc5 so the generated `.smt2` and `.sy` are
read back by a solver rather than only digested.

### PR 3 — documentation

```bash
git checkout -b eoc-docs origin/main
git apply to-main/3-docs.patch
git add -u
git add docs/README.md docs/eos-todo.md proof_pipeline.md
```

No build impact: Markdown only.

---

## Caveats

- **`expected.txt` holds digests of pipeline output.** Never resolve a conflict
  in it by hand or by taking a side; rebuild and run
  `python3 tools/eoc/test/regress.py --update`. When two branches both touch
  the pipeline the correct digests are in *neither* parent — three of ours were
  exactly that.
- **CI is only fully gated after PR 2.** PR 1 is checked by the build and the
  smoke test; the semantics check and the regression arrive with PR 2.
- **`1-eoc-engine.patch` emits one `new blank line at EOF` warning.** Harmless;
  it applies.
- **`semantics-compiler-to-main.patch`** at the repository root is an earlier,
  stale attempt at this same job: it no longer applies, predates the
  `--semantics`/`--smt-semantics` rename and carries no `--calc-name`. These
  supersede it; delete it.
- The patches are a snapshot of `ethosEoc3` at `406b5499`. If the branch moves,
  regenerate with
  `git diff --binary origin/main...ethosEoc3 -- <paths> > to-main/N-name.patch`.
