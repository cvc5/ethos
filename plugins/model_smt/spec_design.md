# Design: fully-Eunoia SMT semantics specification for model_smt

Status: draft design (Aug 2026, branch ethosEoc3).

## 1. Goal

Move the entire per-operator content of `model_smt.cpp` — the ~200 `add*Sym`
registrations, the raw-string auxiliary programs, and the `smtToSmtEmbed`
string rewriting — into fixed, hand-written Eunoia spec files. After the
refactor the C++ knows the *conventions* (naming, section layout, signature
classes) but contains **zero knowledge of any individual SMT-LIB operator and
zero knowledge of CPC**.

Two spec templates:

- `plugins/model_smt/smt_spec.eo` — the fixed SMT-LIB semantics. Part of the
  trusted template set, versioned with the compiler.
- `tools/eoc/cpc/cpc_model_spec.eo` — CPC-specific skolems (`@purify`,
  `@strings_occur_index`, `@quantifiers_skolemize`, `@sets_deq_diff`, ...).
  Staged here for now; ultimately it should live next to `Cpc.eo` in the cvc5
  repo. Other calculi (e.g. alethe: `@cl`) ship their own spec file.

## 2. The key structural observation

For a representative operator (`+`, registered today as
`addConstFoldSym("+", {kT, kT}, kT)`), the generator emits five pieces into
`model_smt_gen.eo`:

| piece | splice marker | mentions user symbol? |
|---|---|---|
| A. embedding decl `$emb_sm.+` / wrapper `$sm_+` | `SMT_TERM_CONSTRUCTORS` | no |
| B. typeof case on `$sm_+` | `SMT_TYPEOF_CASES` | no |
| C. eval dispatch case on `$sm_+` | `SMT_EVAL_CASES` | no |
| D. eval aux program `$smtx_model_eval_+` (+ fwd decl) | `SMT_EVAL_PROGS(_FWD_DECL)` | no |
| E. bridge case `(($eo_to_smt (+ x1 x2)) ($sm_+ ...))` | `EO_TO_SMT_CASES` | **yes** |

(Plus occasionally: F. desugar aux (`$eo_is_list_nil_+`), typeof aux programs,
`$eo_to_smt` aux programs.)

Pieces A–D and F depend **only on the fixed SMT-LIB vocabulary**, never on the
user signature. They can be written once, by hand, in the spec file. Only
piece E names the user's symbol, and its shape is fully determined by the
naming convention plus a small per-argument classification. So:

> **The spec files carry A–D/F verbatim as Eunoia text. The C++ generates
> only E, by convention.**

## 3. Spec file format

A spec file is plain Eunoia text partitioned into *op blocks* by line-level
directives that the assembler consumes (they are `;` comments, so the content
is also valid Eunoia when spliced). Section names are exactly the existing
splice markers in `model_smt.eo`.

```lisp
;;!op + :sig ((@arith @arith) @arith)
;;!section SMT_TERM_CONSTRUCTORS
(declare-parameterized-const $emb_sm.+ ((x1 $smt_Term :opaque) (x2 $smt_Term :opaque)) $smt_Term)
(define $sm_+ ((x1 $smt_Term) (x2 $smt_Term)) ($emb_sm.+ x1 x2))
;;!section SMT_TYPEOF_CASES
  (($smtx_typeof ($sm_+ x1 x2)) ($smtx_typeof_arith_overload_op_2 ($smtx_typeof x1) ($smtx_typeof x2)))
;;!section SMT_EVAL_CASES
  (($smtx_model_eval M ($sm_+ x1 x2)) ($smtx_model_eval_+ ($smtx_model_eval M x1) ($smtx_model_eval M x2)))
;;!section SMT_EVAL_PROGS
(program $smtx_model_eval_+
  ((x1 $native_Int)(x2 $native_Int) (x3 $native_Real) (x4 $native_Real) (t1 $smt_Value) (t2 $smt_Value))
  :signature ($smt_Value $smt_Value) $smt_Value
  (
  (($smtx_model_eval_+ ($vsm_numeral x1) ($vsm_numeral x2)) ($vsm_numeral ($native_z_+ x1 x2)))
  (($smtx_model_eval_+ ($vsm_rational x3) ($vsm_rational x4)) ($vsm_rational ($native_q_+ x3 x4)))
  (($smtx_model_eval_+ t1 t2) $vsm_not_value)
  )
)
;;!section EO_DESUGAR_AUX
(program $eo_is_list_nil_+ ((T Type) (x1 T))
  :signature (T) Bool
  (
  (($eo_is_list_nil_+ x1) (eo::is_eq (eo::to_q x1) 0/1))
  )
)
;;!endop
```

The section bodies above are byte-identical to what the generator emits today
(harvested from a real run) — that is the migration strategy, see §9.

Text outside any `;;!op` block is unconditional: it is spliced whenever the
spec file is loaded (used for shared helpers, and lets `model_smt.eo` core
stay as-is).

### Header directive grammar

```
;;!op <name> [:type] [:sig (<argclass>*) <retclass>] [:alias <desugared-name>]
             [:no-bridge] [:eo-deps (<sym>*)] [:deps (<op>*)]
;;!section <MARKER-NAME>
;;!endop
```

- `<name>` — the SMT-LIB (user-facing) symbol. `@`-names allowed (CPC spec).
- `:type` — this op is a type constructor (`Array`, `Seq`, `BitVec`, ...);
  its embedding uses the `$emb_tsm.` / `$tsm_` prefix and its bridge case goes
  to `$eo_to_smt_type`.
- `:sig` — argument/return classes drawn from the *fixed* vocabulary that
  today lives in the `Kind` vectors and pseudo-kinds:
  `Bool Int Real String Seq StrVSeq BitVec RegLan QInt Type Term Any @arith`.
  Used for (a) the user-declaration compatibility check (§6) and (b) selecting
  per-argument conversions in the generated bridge (§5). It does **not**
  influence evaluation semantics — those are the hand-written sections.
- `:alias` — desugared overload name that maps to this op
  (e.g. `;;!op uneg :alias $eoo_-.2 ...`). The `$eoo_<name>.<k>` scheme itself
  is generic; the per-op fact is spec-side.
- `:no-bridge` — suppress the generated default `$eo_to_smt` case. Used by ops
  with hand-written `EO_TO_SMT_CASES` sections (`=`, `ite`, `distinct`,
  `@quantifiers_skolemize`, ...) and by intentionally-ignored symbols.
- `:eo-deps` — EO-level symbols that must survive the *first* trim when this
  op appears in a signature, because they occur on the *pattern side* of this
  block's `EO_TO_SMT_CASES` (e.g. `@quantifiers_skolemize` pattern-matches
  `(forall x1 x2)`). Rare; see §7.
- `:deps` — explicit extra block dependencies not discoverable by scanning
  (e.g. `Array :deps (const)` for value constructibility — the tail of today's
  `term_reduce_deps.eo`).

### Naming conventions (the contract between user signature and fixed layer)

| user signature | fixed smt layer |
|---|---|
| term op `N` | block `;;!op N`, constructor `$emb_sm.N`, wrapper `$sm_N`, evaluator `$smtx_model_eval_N` |
| type `N` | block `;;!op N :type`, constructor `$emb_tsm.N`, wrapper `$tsm_N` |
| overload `$eoo_N.k` | block carrying `:alias $eoo_N.k` |
| calculus skolem `@N` | block `;;!op @N` in the calculus spec file |

## 4. What each existing table becomes

| C++ today | spec file tomorrow |
|---|---|
| `addConstFoldSym` / `addLitSym` / `addLitBinSym` | hand-written `SMT_EVAL_PROGS` program + dispatch case |
| `addTermReduceSym` / `addRecReduceSym` | hand-written eval program whose body builds `$sm_*` terms |
| `addEunoiaReduceSym`, `d_specialCases`, `d_eoToSmtFullCase` | hand-written `EO_TO_SMT_CASES` section + `:no-bridge` |
| `addTypeSym` | `;;!op N :type` block |
| `addAuxTypeProgram`, `d_typeCase`, `d_typeRetCase`, `d_typeFullCase` | `SMT_TYPEOF_AUX` / `SMT_TYPEOF_CASES` sections |
| `d_auxDef`, `d_auxSmtEval`, `d_auxDesugar` raw strings | sections of the owning op block (or unconditional text) |
| `addAuxIsListNil` | `EO_DESUGAR_AUX` section |
| `printAuxNatRecProgram` | hand-written program in `SMT_EVAL_PROGS` |
| `d_overloadRevert` | `:alias` |
| `d_symIgnore` | block with `:no-bridge` and no sections |
| pseudo-kinds, `smtToSmtEmbed`, `replace_all` hacks | **deleted** — spec text is already at the `$sm_`/`$vsm_` level |

The `SMT_EVAL_PROGS_FWD_DECL` entries are derived mechanically: the assembler
copies the name and `:signature` line of each program appearing in an included
`SMT_EVAL_PROGS` section. (Pure text copy; no semantics in C++.)

## 5. The assembler (all that remains of model_smt.cpp)

1. Load spec files (raw text, exactly like `model_smt.eo` is loaded today).
   Parse directives into blocks; splice unconditional text.
2. **Seed**: iterate `d_declSeen` in parse order. Skip internal names
   (`$...`, `@@...`). Revert overloads generically (`$eoo_N.k` → alias
   lookup). For each remaining symbol:
   - no matching block → `EO_FATAL "no model semantics found for <name>"`
     (the soundness backstop, unchanged);
   - `:sig` incompatible with the declared type (§6) → fatal;
   - otherwise include the block and, unless `:no-bridge`, emit the default
     bridge case: `(($eo_to_smt (N x1 ... xn)) ($sm_N c1 ... cn))` where each
     `ci` is chosen by the argument's class: `$eo_to_smt xi` for term classes,
     `$eo_to_smt_type xi` for `Type`, the nat-validity-guarded form for
     `QInt`, opaque-argument handling driven by the declaration's `:opaque`
     attribute as today.
3. **Semantic closure** (see §7): scan the text of every included block for
   tokens `$sm_<n>`, `$tsm_<n>`, `$smtx_model_eval_<n>`; if `<n>` names a
   block not yet included, include its smt-layer sections (**not** its
   bridge). Repeat to fixpoint. `:deps` adds explicit edges.
4. Distribute all included sections into the `model_smt.eo` markers, seed
   blocks first in decl-seen order (matches today's emission order, enabling
   byte-diff validation), closure blocks after in spec-file order.
5. Substitute markers, write `model_smt_gen.eo`. Unchanged from today.

Datatype handling, `bind()` capture, and output plumbing are already generic
and stay. Estimated size: `model_smt.cpp` 2403 → roughly 500 lines.

## 6. Signature compatibility check (new soundness gain)

Today the `Kind` vectors implicitly pin each operator's expected shape; a pure
naming convention would silently give `and : (-> Int Int Int)` Boolean
semantics. The `:sig` clause closes this hole: the assembler structurally
matches the user declaration's type against the class string — argument count
(modulo `:right-assoc-nil` / opaque conventions, resolved from the decl's
attributes as `finalizeDecl` does now) and type-head names (`Bool`, `Int`,
`Real`, `Seq`, `BitVec`, ..., with `@arith` = Int-or-Real overload, `Any`/
`Term` unconstrained). Mismatch is fatal. Roll-out: warn during migration,
hard error once CPC is clean.

## 7. Trimming becomes two clean layers

Today, `term_reduce_deps.eo` injects ~85 `trim-defs-cmd (depends ...)`
commands so the *first* trim keeps EO-level declarations alive (`xor` keeps
`not`, `=`; `bvsgt` keeps a dozen bv ops) purely so that model_smt later
emits their semantics. That file duplicates the reduction bodies encoded in
C++ strings and is kept consistent by hand — a standing drift hazard — and it
forces symbols into the EO layer that no proof rule mentions.

Under this design the dependency lives where the semantics lives:

- **smt layer (automatic)**: if `xor`'s eval program mentions `$sm_not`, the
  closure in §5 includes the `not` block's smt-layer sections. No EO-level
  declaration, no bridge, no `depends` command — the EO layer of the output
  is untouched. The dep information is *derived from the spec text itself*,
  so it cannot drift.
- **EO layer (rare, explicit)**: only pattern-side occurrences in
  `EO_TO_SMT_CASES` genuinely need the EO symbol declared (e.g.
  `@quantifiers_skolemize` matching `(forall x1 x2)`). These are declared as
  `:eo-deps` and the trim stage consumes them: the driver passes the spec
  files to trim-defs, which reads *only* the block headers and synthesizes
  the few remaining `depends` commands.

Consequences: `term_reduce_deps.eo` is deleted; first-stage trimming gets
more aggressive (EO output shrinks to genuine rule deps); the smt layer of
`model_smt_gen.eo` stays exactly as minimal as today because inclusion is
still per-op, not whole-file.

## 8. Backend impact

None. The `$native_apply_*` / `$native_embed_*` boundary is unchanged;
`lean_meta` and `smt_meta` consume `model_smt_gen.eo` exactly as before. The
known pre-existing `$native_vcmp` gap in `smt_meta.smt2` is orthogonal.

## 9. Migration plan (byte-diff driven)

- **Phase 0 — assembler.** Implement directives, seeding, closure, bridge
  printer behind a `--plugin.model-smt-spec=<paths>` option (comma list,
  plumbed as a driver `--model-spec` flag). With no spec files the legacy
  tables run; output byte-identical trivially.
- **Phase 1 — harvest bootstrap.** Do not hand-transcribe the trusted base.
  One-off script: write a synthetic signature declaring *every* supported
  operator, run today's generator, slice `model_smt_gen.eo` into op blocks
  keyed by the `$sm_<n>` head of each piece. This mechanically produces the
  section bodies (already validated text), leaving only headers (`:sig`,
  `:alias`, `:no-bridge`, `:eo-deps`) to write by hand from the current
  registration calls.
- **Phase 2 — migrate by category**, shrinking the C++ tables stepwise, in
  the order: raw-string aux defs and eunoia-reduce ops → type syms →
  const-fold family → lit/bin/rec reductions (bv, re). After each step:
  byte-diff `model_smt_gen.eo`, VC parse via cvc5, Lean output diff on
  `tests/Arith-rules.eo arith_sum_ub` (and a strings/bv-heavy synthetic sig).
- **Phase 3 — CPC split.** Move `@`-ops to `cpc_model_spec.eo`; land the
  closure + `:eo-deps` trim integration; delete `term_reduce_deps.eo`.
  Validate against real CPC output when available (VC diff should be empty
  or explainable).
- **Phase 4 — cleanup.** Delete legacy tables, pseudo-kinds,
  `smtToSmtEmbed`; promote the `:sig` check to fatal.

## 10. Open questions

1. `:sig` treatment of n-ary/right-assoc-nil ops: check against the SMT-LIB
   binary shape (with nil handling from decl attributes), or against the
   desugared shape? Proposal: the former, since `:sig` speaks SMT-LIB.
2. Exact section granularity for `=`/`ite`/binders currently in core
   `model_smt.eo`: leave in core (always included) vs. give them blocks for
   uniformity. Proposal: leave in core; they are unconditional semantics.
3. Closure token scan: require section-local scanning only, or also scan
   unconditional spec text (which is always included anyway)? Proposal:
   included text only; unconditional text needs no scan.
4. Home of `cpc_model_spec.eo` long-term (cvc5 repo next to `Cpc.eo`) and
   how the driver locates it (`--model-spec` flag vs. convention
   `<sig>.model.eo` next to the input signature). Proposal: support both;
   the convention keeps CPC out of driver defaults too.
