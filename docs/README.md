# Making the Eunoia compiler agile and elegant

This is a map of where `ethos-eoc` is rigid, written to be argued with. It has
two halves and no patches:

- **[The challenge to the user](#part-i--the-challenge-to-the-user)** — everything
  someone has to get right before an `.eo` signature and its `.eos` semantics
  compile, in the order they hit it.
- **[The inner setup](#part-ii--the-inner-setup)** — what the compiler holds fixed:
  which templates are hardcoded, what SMT-LIB is *assumed* to be
  (term / type / value), and where the seam between "configuration" and
  "embedding" actually falls.

Then [Pain points](#part-iii--pain-points), of which `is_list_nil` is the worst,
and [Directions](#part-iv--directions).

Nothing here is a proposal to change code. The point is to be able to say
precisely *what* is hard before anyone argues about how to make it easy.

Reference material this leans on, rather than repeats:
[`proof_pipeline.md`](../proof_pipeline.md) for where the compiler sits,
[`tools/eoc/README.md`](../tools/eoc/README.md) for the driver, and
[`tools/eoc/semantics/README.md`](../tools/eoc/semantics/README.md) for the
configuration language.

---

## The shape of the thing

A user brings two files and gets three targets:

```text
  <calculus>.eo   ──────┐                       ┌──> Lean checker + rule lemmas
  the signature         │                       │
                        ├──> ethos-eoc ─────────┼──> SMT-LIB VC per rule
  <calculus>.eos  ──────┘                       │
  what its symbols                              └──> SyGuS query per rule
  mean to a model
                              ▲
                              │ fixed by the tool
                              │
   smt.eos ── the SMT-LIB target ── model_smt.eo ── natives.eos
   lean.eos ── smt-vc.eos ── eo_desugar.eo ── model_smt.eos ── sem_target.py
```

The claim the tool makes about itself is that the two files on the left are
*description* and everything below the arrow is *compiler*: a second calculus is
a second pair of files, not a change to the tool. Most of this document is about
where that claim holds, where it nearly holds, and the one place it plainly does
not.

---

# Part I — the challenge to the user

## 1. Before either file exists

Five things must line up, and only two of them are checked for you.

| | What | How it is named | Checked? |
| --- | --- | --- | --- |
| 1 | An `ethos-eoc` build — the plugin build, *not* the default `ethos` | `cmake -S plugins -B build-eoc` | driver configures it if absent |
| 2 | The signature to compile | positional argument, or `EOC_CPC_INPUT` | file-not-found only |
| 3 | Its semantics | `--semantics`, or `EOC_SEMANTICS` | **no**: omitting it fails at stage 6, not at launch |
| 4 | The SMT-LIB semantics it is written against | `--smt-semantics`; defaults to `semantics/smt.eos` | ships with the tool |
| 5 | `cvc5` for parse checks | `--cvc5`, `$CVC5`, `PATH`, or `--skip-cvc5` | yes, at launch |

Two traps live here.

**The default input is a path into someone else's tree.** `EOC_DEFAULT_CPC_INPUT`
in [`tools/eoc/cpc/common.sh`](../tools/eoc/cpc/common.sh) is
`<repo>/../cvc5-ajr/proofs/eo/cpc/Cpc.eo` — a sibling checkout, by that name.
The CPC wrappers work on the machine that has it and nowhere else.

**Input paths resolve against your shell, not the build directory.** The driver
writes to `tools/eoc/out/` and reads relative to `$PWD`, so the same command
from the build tree and from the repo root are different commands.

## 2. The signature side (`.eo`)

Most of a Eunoia signature compiles with nothing said about it. What the user
has to know is the list of things that *do* require an answer somewhere else:

- **Every declared symbol needs a meaning.** A symbol the semantics file says
  nothing about is fatal, by design:
  `ERROR: no model semantics found for <name>`
  ([`plugins/model_smt/model_smt.cpp:71`](../plugins/model_smt/model_smt.cpp)).
  The comment above it is explicit that this is a soundness check, not a
  nicety. Names beginning `$` or `@@` are exempt as signature-internal.
- **Every n-ary operator needs a nil predicate** — but only sometimes, and the
  rule for *when* is not written on the operator. See
  [is_list_nil](#10-the-is_list_nil-hack) below; this is the pain point.
- **Every recursive program the Lean backend cannot see terminating needs a
  termination clause**, hand-written as literal Lean text under `:lean`.
- **Anything SMT-LIB has no model for must be excluded by name** — `lambda`,
  its beta-reduction rule, and their private helpers, in CPC's case. The list is
  literal; the compiler computes no dependency closure, so every declaration
  that goes with an excluded one has to say so for itself.

## 3. The semantics side (`.eos`)

The configuration language is well documented and genuinely small — nine forms
and nothing else. The burden is not the grammar. It is that writing a correct
block means holding four things in your head at once:

**(a) Which of the nine forms.** `define-symbol`, `define-sort`,
`declare-constructor`, `define-literal`, `define-method`, `define-rule`,
`program`, `define-macro`, `section`. Three of them (`define-sort`,
`declare-constructor`, `define-literal`) are
*target-only* — legal in `smt.eos`, refused in an input's set. Two
(`define-method`, `define-rule`) are *input-only*. Nothing in the form itself
says which; it is the role the file was named under.

**(b) Which aggregates the symbol contributes to.** For an input's symbol,
usually none — the `term` aggregate's default covers it. For a target symbol, a
`:typeof` and either `:eval` cases or a `:value`.

**(c) What level each sub-term is at.** Four vocabularies, and *which one you
are in is never written down* — it is read off the type of the place the term
stands in:

| level | said by | `f` compiles to | `0` compiles to |
| --- | --- | --- | --- |
| native | a `"..."` type | must be bound | `$native_z_zero` |
| value | `SmtValue` | `$smtx_model_eval_f` | `$vsm_z_zero` |
| term | `SmtTerm` | `$sm_f` | `$sm_z_zero` |
| type | `SmtType` | `$tsm_f` | — |

Plus two with no names of their own: `embedding` and `input`. This is elegant
in the small — you never say a level twice — and it means the same three
characters mean four things depending on context. The compiler answers with the
name to use instead when you get it wrong, which is the redeeming feature: the
six refusal families in
[Casting](../tools/eoc/semantics/README.md#8-casting) each name their own fix.

**(d) Which layer prefix.** `smt.` for the SMT-LIB signature, `eo.` for the
input as the desugar stage embeds it, both defined as macros in an
`embedding.eo` of the set. A transformation reads `eo.` and writes `smt.`.

`smt.eos` is 132 symbols, 9 sorts, 14 values, 5 literals, 12 methods and 68
programs across 1,837 lines. `development-cpc.eos` is 182 symbols and 26
programs across 1,123 lines. That is the working scale.

## 4. What is checked, and what is not

The compiler is thorough about *reference*:

- every helper a block names is written out by some file of the same set;
- a name a case does not bind is an error;
- a native exists and has the right arity;
- a type of the embedding exists;
- no block uses a name a later block defines;
- `--check` reports STALE / MISSING against the generated files.

It says nothing about *meaning*. The gaps that matter:

| Not checked | Consequence |
| --- | --- |
| That an `:is-list-nil` predicate actually characterises the operator's nil | silent divergence from what ethos itself does — see §10 |
| That a `:eval` case models SMT-LIB correctly | a wrong model gives a wrong verdict, `unsat` and all |
| That a `:lean` termination clause is sound | Lean catches it, one full regeneration later |
| That an exclusion list is closed under dependency | a later stage names something that was dropped |
| That a forward-declared program is ever defined | SMT backend: a free uninterpreted function. Lean: a name that was never written |
| That the natives a stage prints exist in the backend's layer | Lean or cvc5 reports it, not the compiler |

The design is deliberate — `tools/eoc/README.md` says outright that "the
generated file is not what says whether a name exists" — but the effect on a
user is that a whole class of mistake surfaces two tools downstream, in a
language they were not writing in.

## 5. The feedback loop

This is the agility problem stated plainly. Adding one symbol to a calculus and
seeing whether it worked costs:

```text
edit .eos  ->  sem_compile.py  ->  desugar  ->  trim-defs  ->  model-smt
           ->  smt-meta / lean-meta  ->  cvc5 / Lean says whether it was right
```

There is no way to ask "is this one block well-formed against the embedding"
short of compiling the set, and no way to ask "does this block mean what I
think" short of running a backend. `sem_compile.py --check` answers a
different question — whether the generated files are current.

What exists and helps: `tools/eoc/test/regress.py` byte-compares the whole
output of a small signature, so a *refactor* is cheap to validate even though
an *extension* is not. Note the asymmetry — the tool is well set up for the
change that must not alter behaviour, and poorly set up for the change that
must.

What does not exist: the whole-signature path is not covered by anything in
this tree. No signature here is one that `smt.eos` covers entirely, so
`lean --all` over a local signature stops at the first symbol with no meaning.
Exercising that path requires the calculus of another repository.

---

# Part II — the inner setup

## 6. What SMT-LIB is assumed to be

The compiler is calculus-agnostic and *target-specific*. The target — SMT-LIB —
is hardcoded as a three-language deep embedding in
[`plugins/model_smt/model_smt.eo`](../plugins/model_smt/model_smt.eo), 1,150
lines that no configuration may add to:

```text
$smt_Term   an SMT term        constructors $emb_sm.X,  applied by $sm_X
$smt_Type   an SMT type        constructors $emb_tsm.X, applied by $tsm_X
$smt_Value  an SMT value       constructors $emb_vsm.X, applied by $vsm_X
```

with, beneath the values, the shapes a value is built over — `$smt_Map` (which
is what an array *and* a set are), `$smt_Seq` (which is what a string is),
`$smt_RegLan`, `$smt_Datatype`, `$smt_DatatypeCons`, `$smt_DatatypeDecl`.

Wider still, a term carries a **meta-kind** saying which layer it embeds in:
Eunoia term, SMT term, SMT type, SMT value, map or sequence value, builtin,
proof, checker rule, command — see `MetaKind` in
[`plugins/utils.h`](../plugins/utils.h). The three `$native_embed_eo`,
`$native_embed_smt`, `$native_embed_checker` markers in the templates are what
assign it.

The decisions frozen into that file, which a *different* target would have to
relitigate:

- values are disjoint from terms, and a model is a map from the one to the other;
- a **function** value is not a map value: `$vsm_Fun` carries a name and the two
  halves of its type, and applying one is handed to the native `eval_fun_apply`;
- applying a datatype constructor is left alone, being the Herbrand term it denotes;
- types answer three questions and exactly three — well-founded, bounded,
  default value;
- `ite` and `=` are ordinary symbols of the configuration that say `:keep`,
  so a signature trimmed to a handful of rules still has them.

The last is a nice piece of design and worth naming: *nothing* is privileged by
the embedding except the shapes. Even equality is a configuration entry.

## 7. The templates

Every stage is a hardcoded template with `$MARKER$` holes that C++ fills. This
is the compiler's actual architecture, and it is worth seeing all at once:

| Stage | Template | Holes | What is fixed in it |
| --- | --- | --- | --- |
| desugar | [`plugins/desugar/eo_desugar.eo`](../plugins/desugar/eo_desugar.eo) (661 ln) | 16 | the Eunoia deep embedding: `$eo_List`, list operators, `$eo_nil`, `$eo_is_list_nil`, `$eo_typeof`, datatypes |
| desugar | [`eo_desugar_native.eo`](../plugins/desugar/eo_desugar_native.eo) (924 ln) | — | the SMT-like builtins of Eunoia, `eo.Term`, the `$emb_X` constructors |
| desugar | [`native_embed.eo`](../plugins/desugar/native_embed.eo) (122 ln) | — | `$native_apply_N`, `$native_type_N`, type aliases; includes `native_defs.eo` |
| desugar | [`eo_desugar_checker.eo`](../plugins/desugar/eo_desugar_checker.eo) (265 ln) | — | the executable checker |
| model-smt | [`plugins/model_smt/model_smt.eo`](../plugins/model_smt/model_smt.eo) (1,150 ln) | 18 | the SMT term/type/value embedding above |
| smt-meta | [`plugins/smt_meta/smt_meta.smt2`](../plugins/smt_meta/smt_meta.smt2) (224 ln) | 2 scopes | the SMT-LIB preamble |
| lean-meta | `plugins/lean_meta/*.lean` (11 files, 932 ln) | 3 scopes | the Lean module layout |

The markers in `model_smt.eo` are all written **commented out** — `;$EO_TO_SMT_CASES$`
— and substitution replaces the comment character along with the marker. That
is what lets the template parse as it stands, which is what lets `smt.eos` be
written in the vocabulary the template declares. Small trick, large payoff:
the embedding is checkable on its own.

## 8. The aggregate table

The one genuinely extensible axis. An *aggregate* is a big program in a
template that every symbol contributes one case to. Which aggregates exist is
declared in [`plugins/model_smt/model_smt.eos`](../plugins/model_smt/model_smt.eos)
and how a case is written in
[`tools/eoc/sem_target.py`](../tools/eoc/sem_target.py). The stage that reads
the generated file knows no aggregate by name — it reads the head of the file:

```text
; $eoc-aggregate $smtx_typeof $eoc_typeof_ $SMT_TYPEOF_CASES$
```

So adding an attribute a symbol may carry is three edits — declaration, marker,
shape — and **no C++ change and no rebuild**. That is the part of the design
that works, and the model for everything else.

The full set today:

| Aggregate | Case | Level | What it answers |
| --- | --- | --- | --- |
| `$smtx_typeof` | `$eoc_typeof_` | type | the type of a term |
| `$smtx_model_eval` | `$eoc_eval_` | value | the value of a term in a model |
| `$smtx_typeof_value` | `$eoc_value_typeof_` | type | the type of a value |
| `$smtx_value_canonical` | `$eoc_value_canonical_` | native | whether a value is written the one way |
| `$smtx_type_wf_rec` | `$eoc_type_wf_` | native | whether a type's values are a set |
| `$smtx_type_bounded` | `$eoc_type_bounded_` | native | whether they are finitely many |
| `$smtx_type_default` | `$eoc_type_default_` | value | the value a model names for a type |
| `$eo_to_smt` | `$eoc_transform_` | term | what a symbol of the input becomes |
| `$eo_to_smt_type` | `$eoc_transform_type_` | type | what a type constructor becomes |
| **`$eo_is_list_nil_`** | **`$eoc_is_list_nil_`** | **input** | **whether a term is an operator's nil** |

Nine of the ten are about the model. Read the last row again — it is the
subject of the next section.

## 9. Where the seam actually falls

The tool's own statement of the line is: *a configuration says what a theory
**does**; a template says what the embedding **is**.* Held to, that would make
every calculus a pair of files. Four things cross it today:

1. **`is_list_nil`** — a desugar-stage obligation carried in a model-semantics
   file. §10.
2. **The `defs_head` side channel.** `sem_compile.py` writes `$eoc-exclude` and
   `$eoc-depends` lines above the first block of the generated file; `driver.py`
   greps them back out (`defs_head`, `defs_excludes`, `defs_depends`, around
   [`tools/eoc/driver.py:407`](../tools/eoc/driver.py)) and re-emits them as
   `(echo "...")` commands into temporary `.eo` files that are written, passed,
   and unlinked. A stage learns what a signature excludes by way of a comment,
   a Python regex, a temp file and an echo command.
3. **Termination clauses.** Literal Lean text in `:lean` attributes of a
   semantics file, gathered into `.lean` files, appended by the lean-meta stage
   to the program it names. Unavoidable — no measure the compiler could guess
   would do — but it means an `.eos` file contains a second language.
4. **The native layer split.** A native is declared in `natives.eos`, spelt
   five different ways depending on where it appears (see the table in
   [`tools/eoc/README.md`](../tools/eoc/README.md#what-one-native-is-called)),
   and implemented separately per backend. The mapping is centralised in
   `LAYERS`, but a user adding an operator touches three files in two
   languages.

---

# Part III — pain points

## 10. The `is_list_nil` hack

This is the worst thing in the compiler. It is worth working through in full,
because every one of its symptoms is a different structural problem.

### What it is for

Eunoia n-ary operators declare a nil terminator: `and` is `:right-assoc-nil true`.
List operations need to ask "is this term the nil of `f`?", and
`$eo_is_list_nil` answers. It is called from `$eo_get_nil_rec` and
`$eo_list_singleton_elim_2` in
[`plugins/desugar/eo_desugar.eo`](../plugins/desugar/eo_desugar.eo), which
means it is load-bearing for every list operator in every n-ary calculus.

Its meaning is not in dispute. The template says so itself:

> `($eo_is_list_nil f x)` is equivalent to `(eo::eq (eo::nil f (eo::typeof x)) x)`.

### Why it is a problem

When the nil is **ground**, the desugar stage just prints it:

```lisp
(($eo_is_list_nil and true) true)
```

When the nil **depends on the type** — `str.++` whose nil is `""` at strings and
`(seq.empty T)` at sequences; `bvadd` whose nil is a zero of the operand's
width; `+` whose nil is `0` or `0.0` — the correct definition needs
`eo::typeof`, and the compiler declines to call it. `optionFwdDeclIsListNilNground()`
at [`plugins/desugar/desugar.cpp:33`](../plugins/desugar/desugar.cpp) returns
`true`, unconditionally. The principled branch is right there at line 419 and
is dead code:

```cpp
d_eoIsListNil << "nil) (eo::eq nil ($eo_nil " << cname
              << " ($eo_typeof nil))))" << std::endl;
```

So instead the stage emits a **forward declaration with no body** —

```lisp
(program $eo_is_list_nil_str.++ ((T Type)) :signature (T) Bool)
```

— and waits for someone else to define it. That someone is the human writing
the semantics configuration:

```lisp
(define-symbol str.++ (s t)
  :is-list-nil (seq.empty T) true
  :is-list-nil             (eo::eq s ""))
```

which `sem_compile.py` renders into `user_defs.eo` and the model-smt stage
splices in at `;$EO_DESUGAR_AUX$`, the first hole of `model_smt.eo`, above
everything else in the file.

### Five things wrong with that

**It inverts the direction of the compiler.** Every other block says what a
symbol means *to a model*. This one says what a symbol means *to a stage that
already ran*. `sem_target.py` says so in its own comment: *"the one thing a
block says to a stage other than the model."*

**It is the only aggregate that breaks all three conventions at once.**
- The only one at `level='input'` — bodies are emitted verbatim in the input's
  own vocabulary, so none of the level machinery of §3(c) applies to it.
- The only one marked `:whole` in `model_smt.eos` — its program is emitted
  under its own name rather than having cases spliced into an aggregate, which
  required a fourth optional word in the `$eoc-aggregate` line and a
  `d_whole` branch in `defs_reader.cpp`.
- The only `$eoc_` name that survives into the generated file: everything else
  is a compile-time label, this one is renamed `$eoc_is_list_nil_X` →
  `$eo_is_list_nil_X` and emitted.

**It lands in the wrong file for the wrong reason.** The only reason a *desugar*
obligation lives in a *model semantics* file is phase ordering: desugar is
stage 5, the semantics files are read only by stage 6, and there is no stage-5
configuration input at all. The `;$EO_DESUGAR_AUX$` hole exists solely so that
stage 6 can retroactively fill in stage 5's holes. Its comment in the template
reads, in full: `;;; remaining desugar definitions e.g. is_list_nil`.

**Nothing checks it.** The desugar stage decides *whether* to forward-declare by
looking at the signature — is the nil term non-ground? The configuration decides
*whether* to define by whether a human typed `:is-list-nil`. These two decisions
are made in different tools, in different languages, from different inputs, and
nothing compares them — the model-smt stage checks that every *declared symbol*
has a meaning and that no `$eoc_` label went unexpanded, neither of which sees a
forward declaration left without a body. So:
- Forgot the attribute → an undefined program reaches the backends. Under SMT,
  a free uninterpreted function the solver may instantiate as it likes. Under
  Lean, a name that was never written.
- Wrote it wrong → the compiled artifact's list semantics silently disagree with
  what ethos itself does when checking a proof. The whole pipeline exists to
  establish that the checker is sound; this is a hand-written, unverified
  predicate sitting inside it.
- Wrote it for a ground-nil operator → a definition nothing uses.

**It scales with the calculus.** Ten `:is-list-nil` attributes across nine
symbols in `development-cpc.eos` today — `+`, `*`, `bvand`, `bvor`, `bvxor`,
`bvadd`, `bvmul`, `str.++` (which needs two), `@@TypedList.cons`. Every n-ary
operator with a polymorphic unit that anyone ever adds is another one, and the
failure mode for forgetting is silence.

### The honest summary

The root cause is one design decision — *the desugar stage may not call
`eo::typeof`* — and everything above is the cost of routing around it. That
decision has a defensible motivation: `$eo_typeof` in the desugared output is
itself an approximation, monomorphised per partial application (`(= x)` has a
type rule, `=` does not), and making a *soundness-relevant* predicate depend on
an approximation is worse than making it depend on a human. But the price is a
hand-written unverified axiom per operator, an aggregate that violates every
convention the others share, and a hole in the model template whose only job is
to patch a stage that already finished.

## 11. The others, briefly

**`eo::typeof` is an approximation with no marker.** The desugar stage
monomorphises partial applications, so the generated type system agrees with
Eunoia's on the cases it generated and is silent elsewhere. Nothing in the
output says which is which.

**One set per role, global filenames.** A run compiles exactly one input set
and one target set, and *where* a set compiles to is fixed by its role:
`user_defs.eo` and `smt_defs.eo`, always. Two calculi cannot be compiled
concurrently in one tree, and a set named with `--semantics` overwrites what
the shipped one would have written. This is stated as a feature — "no stage can
read one semantics' file while another is in use" — and it is also why parallel
CI over two calculi is not a thing.

**Exclusions are literal and unclosed.** `:exclude` names are matched by string.
No existence check, no dependency closure. Excluding `lambda` means also finding
and excluding its rule and its helper methods by hand, and a typo excludes
nothing at all, silently.

**The trim dependency channel.** `trim-defs` needs to know that
`@quantifiers_skolemize`'s transformation mentions `forall`, or it will trim
away a symbol a generated case names. That information travels as a
`$eoc-depends` comment in a generated file, grepped by Python, re-emitted as an
echo command. It works. It is four representations of one edge.

**Termination clauses are Lean text in an `.eos` file.** Necessary, but it means
the semantics language has an escape hatch into a second language with no
checking, and the failure surfaces only when Lean runs.

**The natives spelled five ways.** Correct, centralised in `LAYERS`, and still
five spellings a user has to recognise when reading a stack trace.

---

# Part IV — directions

Sketches, in rough order of value-to-cost. None is a plan.

A shorter and more concrete list -- attributes of the configuration language
that carry a fact the compiler could carry itself, or half of one, with what
deleting each would take -- is in [`eos-todo.md`](eos-todo.md). Item 1 below is
what dissolves most of it.

**1. Give the desugar stage a configuration input.** The single change that
dissolves §10. If stage 5 could read a set of its own, `:is-list-nil` would
live there, `;$EO_DESUGAR_AUX$` would go away, `:whole` and `level='input'`
would stop being exceptions, and the aggregate would stop being the one that
talks backwards. Everything else in this list is smaller.

**2. Close the loop on `is_list_nil` specifically.** Independent of (1): the
desugar stage knows exactly which operators it forward-declared. Emit that list;
have `sem_compile.py` or the driver diff it against the `:is-list-nil` blocks
and refuse a mismatch in either direction. This is cheap and removes the silent
failure, though not the hand-writing.

**3. Verify the predicate rather than trusting it.** The intended meaning is
written down — `(eo::eq (eo::nil f (eo::typeof x)) x)`. That is a proof
obligation, and the tool already generates proof obligations. Emitting one VC
per `:is-list-nil` block would move it from a trusted axiom to a discharged
lemma.

**4. A checkable unit smaller than a set.** Today the smallest thing you can ask
about is a whole configuration. A `sem_compile.py --explain <symbol>` that shows
what one block compiles to — every program, every case — would turn §5's
edit-compile-backend loop into an edit-look loop for the common mistakes.

**5. Make the exclusion list closed and checked.** Verify each name exists;
compute the closure. Both are cheap, and the current behaviour fails silently in
the direction of "compiled something wrong" rather than "refused".

**6. Replace the head-comment side channel with a real one.** `$eoc-exclude`,
`$eoc-depends`, `$eoc-aggregate` are three protocols riding in comments, read by
a mix of Python string splitting and C++ parsing. One sidecar file with one
reader would say the same thing once.

**7. A second target, to find out what "target-agnostic" would cost.** The
term/type/value split of §6 is SMT-LIB's shape. Nothing has ever tested whether
it is *the compiler's* shape or *SMT-LIB's*, because there has only ever been
one target. That question is answerable and currently unanswered.

**8. Say what a target's language already brings, and check the natives against
it.** A layer owes the embedding a definition for every native except the ones
that say `:is`, the ones that forward to a literal, and the ones the target
*already has* -- `and`, `or`, `not`, `ite` and `to_real` are SMT-LIB's own. The
third of those is written nowhere, so nothing can tell a native a target gets
for free from one that is simply missing, in either direction: an unimplemented
native surfaces as a Lean or cvc5 error two tools downstream, and a layer entry
for a native no longer declared is dead text nothing reports. One line per
target naming what its language brings would make both checkable, and only the
natives a run actually reaches need checking, which the run already knows. The
measured state is in
[`tools/eoc/README.md`](../tools/eoc/README.md#what-a-layer-owes-the-embedding).

---

## Stretch: `eo::native` in the front end of ethos

**The natives are a closed vocabulary, and only the compiler may extend it.**
`plugins/desugar/natives.eos` declares 66, and a signature may name those and
nothing else. A calculus that wants an operation its target has and Eunoia does
not -- a Lean method, an SMT-LIB function -- cannot say so: the native has to be
added to `natives.eos` and to each backend layer, and that is a change to the
compiler rather than to the signature. It is the one place where "a second
calculus is a second pair of files" is plainly false.

`eo::native` would be the front end of ethos accepting a target operation named
directly:

```lisp
(eo::native "Nat.gcd" x y)
```

ethos does not know what `Nat.gcd` is and does not need to. It carries the term
-- opaquely, the way it already carries `$native_apply_N` -- and the backend
emits `Nat.gcd x y`. What changes is *who may name one*: the natives stop being
the compiler's closed list and become the signature's open one.

**Why this is the agility item.** Everything else in this document is agility
for the tool: fewer names welded into C++, more of the embedding stated as
configuration. None of it shortens the loop a calculus author is in, because
none of it is something they write. This is. A signature reaching a target
operation directly is the difference between "add it to the compiler and
rebuild" and "write it".

**What it makes load-bearing.** Direction 8 above is optional while the natives
are closed and curated -- a missing one is a mistake in *our* files, caught the
first time anything compiles. Once a signature may name any operation at all, a
name that the target does not have is a mistake in a *user's* file, and there is
nothing left to catch it but the check: what each target's language brings, and
whether the operation named is in it. Opening the vocabulary is what turns that
check from a tidy-up into a requirement.

**What it does not get you.**

- **No evaluation.** ethos cannot compute with a term it does not understand, so
  an `eo::native` term is inert in the front end: usable where a signature
  builds or transmits a term, not where a program must reduce one. That is the
  same restriction `$native_apply_N` has today, made visible to the user.
- **No meaning to a model.** The model-smt stage refuses a symbol the semantics
  says nothing about, by design and for soundness. An `eo::native` term is a
  symbol like any other in that respect: naming a Lean method does not say what
  it denotes, so a verification condition over one is about an uninterpreted
  function until the semantics says otherwise.
- **No type.** Eunoia would have to be told what the operation takes and
  returns, since it cannot read that off a name in someone else's language.

So the shape of it is: a signature names the operation and says its type and its
meaning; the compiler checks the target has it; the backend emits it. Two of
those three are things the pipeline already does for a declared symbol. Only the
middle one is missing, and it is direction 8.
