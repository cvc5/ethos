# Noesis, from the compiler side

An answer, from the tree that holds `ethos-eoc`, to the entry
[`noesis`](https://github.com/ajreynol/anoieu/blob/main/tools/ynoia/tools.md)
in ynoia's register of tools that do not exist — *the semantics and the
compiler, defined in Lean*, with a theorem relating what the compiler emits to
what the semantics says.

That entry states where its difficulty sits: **"A compiler-correctness theorem
needs a semantics of *Eunoia*, and there is not one."** It is right, and it is
the field this document is about. The compiler tree can say something specific
about it that the account, written from outside, could not: how much of that
semantics already exists here, in what form, and what it would take to find out
whether it is correct.

Written against the criteria of [`README.md`](README.md) — a configuration says
what a theory *does*, a template says what the embedding *is* — and in the
vocabulary of
[`why-eunoia.md`](https://github.com/ajreynol/anoieu/blob/main/tools/ynoia/why-eunoia.md),
whose objection and open-question numbers are used below without restating
them.

**This decides nothing.** ynoia's pages decide nothing by policy and this one
inherits that: it reports what is in this tree, argues about where two entries
should sit, and recommends work no one has promised. Where reading turned up
something wrong in somebody else's file, that is a finding and leaves through
the reporting workflow, not through here. Nothing below is a finding.

---

## The short version

1. **There is a semantics of Eunoia in this tree.** It is 1,215 lines of
   Eunoia, it is what every downstream artifact is already generated against,
   and it has never been compared with the C++ that is the other definition.
   Noesis's blocker is therefore not *write one* but *validate the one that
   exists* — a different and much cheaper first task.
2. **The relation that would validate it runs today, with no new tooling.**
   `ethos S` against `ethos (desugar S)` over the in-tree corpus: 77
   verdict-bearing signatures, **68 agree, 0 disagree, 9 the desugar stage
   cannot process at all**. Measured for this document; nothing in the tree
   reports it.
3. **Four of those nine are `is_list_nil`** — the exact failure ynoia's **O6**
   names as what the arrangement's cost looks like in practice, reproduced from
   ethos's own test suite, surfacing as a lexer error on a generated file two
   stages downstream.
4. **Open question 7 — where the line falls between the invariant core and what
   a signature contributes — can now be read off this tree** rather than
   argued. That is noesis's stated prerequisite, and the `ethosEoc3` work made
   the line data instead of judgement.
5. The theorem worth wanting first is probably not the compiler-correctness
   one. It is **per-run validation of the artifact**, which the same
   restructuring made lemma-shaped, and which is an increment rather than a
   fork.

---

## 1. The semantics exists, and nothing has ever checked it

Eunoia is written down twice in this repository:

| | what it is | size |
| --- | --- | --: |
| `src/` | the parser, type checker and evaluator — normative de facto | 10,278 C++ |
| `plugins/desugar/eo_desugar*.eo`, `native_embed.eo` | what `eo.Term` is, what the `$emb_X` constructors are, what each `eo::` builtin does | 1,215 EO |

The second is a formal semantics of Eunoia, written in Eunoia, and it is not a
sketch: it is the definition every verification condition and every line of
generated Lean is produced against. `proof_pipeline.md`'s known gaps —
`eo::typeof` approximating rather than reproducing the internal type system, the
`:chainable` and assoc desugarings mirrored in three places with nothing
comparing them — read as isolated defects but are instances of one structural
fact: **the two definitions are independent and nothing relates them.**

This changes noesis's opening move. The entry's *Costs* field reads as though
the semantics has to be written from nothing, and estimates the size of the job
from "this repository's desugarer is a partial and informal answer to one corner
of that question". The corner is larger than that suggests, and the first task
is not authorship. It is deciding **which of the two is normative** and building
the comparison — after which noesis's Lean definitions would be a port of a
validated artifact rather than a first draft of an unvalidated one.

My recommendation, offered as this tree's opinion and not as a decision:
**declare the embedding normative and make `ethos` accountable to it.** It is
mostly written, it is already the thing downstream depends on, and it converts
"the two might have drifted" from a worry into a test. Writing a third semantics
in Lean before validating the second is how you end up with three.

## 2. The relation, run

The cheapest statement of that comparison is available now. Stages 5 and 6 are
**endogenous** — Eunoia to Eunoia — so meaning-preservation for the largest
imperative pass in the compiler is a claim ethos itself can adjudicate:

> for every signature `S` and proof `p`, `ethos S p` and `ethos (desugar S) p`
> agree.

`tests/` holds 204 self-contained signature-and-proof files that ethos already
runs to a verdict. Running the relation over the first 80 by name:

| | |
| --- | --: |
| verdict-bearing signatures | 77 |
| **agree** | **68** |
| **disagree** | **0** |
| desugar stage refuses the input | 9 |

Zero disagreements on the covered part is the first evidence anyone has that the
Eunoia embedding and the C++ agree on anything. The nine are the interesting
output, because **the coverage of the desugar stage against ethos's own test
suite is not measured anywhere**:

| test | what comes out |
| --- | --- |
| `Strings-programs`, `Strings-theory` | `Could not find symbol $eo_is_list_nil_str.++` |
| `ff-nil` | `Could not find symbol $eo_is_list_nil_ff.add` |
| `homogeneous-list-ops` | `Could not find symbol $eo_is_list_nil_@@TypedList.cons` |
| `Datatypes-theory`, `Sets-theory` | `Expression of unexpected type` |
| `bv-extract-smt3` | `Unexpected free parameter in expression` |
| `bv-type-strict` | `Parsed type cannot contain evaluation in this context` |
| `eo-definitions-test` | `Forward declaration of program $eo_nil had different type` |

Every one arrives as a fatal error from `src/lexer.cpp` naming a line of a
generated file. None arrives as the stage saying what it could not do.

**On the first four.** `development-cpc.eos` is a *test* semantics and says
nothing about strings or finite fields, so it writing no `:is-list-nil` for
`str.++` is not a defect in it. The failure *mode* is the point: the desugar
stage forward-declares a predicate for every n-ary symbol it sees, the set
supplies nine, and nothing compares the two lists. That is
[`eos-todo.md`](eos-todo.md)'s **"Still open here"** and Part IV item 2 of
[`README.md`](README.md) — *"Diff them and refuse a mismatch in either
direction"* — and it is ynoia's **O6** quoted almost verbatim. The relation
produced four live instances of it in twenty minutes.

This relation is one of the five ynoia lists under
[`elenchos`](https://github.com/ajreynol/anoieu/blob/main/tools/ynoia/why-eunoia.md)
as *metamorphic relations with content*: "a signature and its desugared form".
It needs none of elenchos's expensive half — no instrumentation, no generator,
no scheduler — and it has a corpus already in the tree. If elenchos is the entry
somebody could start on a Monday, this is the part they could finish on the
Monday.

## 3. Three refinements to the account

Offered as corrections to statements that were accurate when written, not as
disagreements with what they were arguing.

**O3 is right about the labour and wrong about the trust.** The Lean
termination measures are hand-written text carried in `.eos`, and a missing one
does surface a full regeneration later — that cost is real. But Lean *checks*
`termination_by`; a wrong measure does not produce a wrong theorem, it produces
a build error. So O3's cost is latency and toil, not trusted surface, and it
should not be priced as a soundness hole. The genuinely soundness-shaped
neighbour is elsewhere: stage 7a does not establish well-foundedness, and
`proof_pipeline.md` is explicit that this makes it **report a spurious
unsoundness** — it errs toward false alarm, never toward accepting an unsound
rule. Worth stating precisely, because "termination is nobody's job" is easily
heard as a claim about what could be believed on false grounds, and neither half
of it is that.

**O6's exemplar has moved since the account was written.** `:whole` is deleted,
`plugins/desugar/desugar.eos` exists, and `is_list_nil` compiles to a file the
desugar stage reads rather than into a hole in the *model* template that a later
stage filled in for an earlier one. Both halves of the predicate are now in one
stage, which is what makes item 2 cheap. O6's general claim stands; its
illustration is half-closed, and the remaining half is small enough that leaving
it open is now a choice.

**O2 got quantitatively worse and structurally better, and only the second
matters.** The `.eos` layer grew: 51% of what the pipeline is told was
configuration and 58% is. Read as "the second bespoke language is expanding",
that is O2 getting stronger. Read structurally it is the opposite, and this is
the one place where I think the account under-reads the evidence. What moved
into configuration is *per-symbol blocks with declared aggregates* — a
`define-symbol` compiles to a named, enumerable set of programs and cases, and
`defs_reader` splices rather than transforms. Under arrangement **B** those
blocks are not thrown away; they are the shape the Lean definitions take, the
aggregate table is the pattern match T1 says it becomes, and the per-block
structure is what makes a compiler theorem's induction have something to
induct over. The `.eos` layer is the tell, and it is also the draft.

## 4. Open question 7 can now be read off this tree

Noesis's *Before it* field names open question 7 — where the line falls between
the invariant core and what a signature contributes — and says it "has to be
answered first, because a compiler's correctness theorem quantifies over
signatures and cannot be stated without it".

The `ethosEoc3` work did not answer that question in prose. It made the answer
**data**, which is better, and the answer can now be read out of the tree:

| | before | after |
| --- | --: | --: |
| constructor and marker names hardcoded in the model-smt stage | 11 | **0** |
| constructors of the embedding's datatypes declared in `model_smt.eo` | 20 | **0** |
| programs over datatypes written in `model_smt.eo` | 25 | **2** |
| `model_smt.eo`, the last hand-written Eunoia describing a *target* | 697 EO | **336 EO** |
| index arities the embedding can express | exactly 3 | **as many as declared** |

`declare-embed-datatype` and `declare-constructor` say what a constructor of an
embedding datatype is called and which datatype it builds, so the model-smt
stage holds no such name; the two programs left in the template are left for
stated reasons. The split that remains is legible: **1,215 lines say what
Eunoia is, 336 say what a target is, and 3,185 lines of configuration say what a
theory does.** Whether that is *the right* line is still a judgement — but it is
now a judgement about a boundary somebody can point at, rather than one about
where a boundary might be drawn if it existed.

So noesis's prerequisite is not discharged, but it is much closer to
discharged than the entry assumes, and the work that closed the gap was done for
unrelated reasons. That is an argument for the entry moving up, and moving an
entry is the whole of what it costs to disagree with that page.

## 5. Which theorem — and the cheaper one beside it

"A verified Eunoia compiler" is three projects.

| | what it verifies | scale |
| --- | --- | --- |
| verify `ethos` | 10,278 C++ | CompCert |
| verify `ethos-eoc` — **noesis** | 5,430 C++ + 2,026 Python | CompCert, and blocked on §1 |
| make the *output* self-certifying | one artifact per run | an increment |

The third is translation validation: the compiler emits evidence that *this*
artifact means what *this* input means, and the evidence is checked. It is
reachable for a specific reason, and the reason is §3's last paragraph. Before
the configuration restructuring, the unit of compilation was "the whole
signature, through 1,347 lines of C++ decisions", and there was nothing to state
a lemma *about*. Now a block goes in and a named set of blocks comes out. That
is a lemma-sized obligation, and the aggregates are the induction.

It also decomposes the compiler usefully, which the whole-compiler framing does
not:

| pass | LOC | correctness is |
| --- | --: | --- |
| `linear_patterns` | 176 | **provable** — crisp spec, small, purely syntactic |
| `trim_defs` | 757 | **checkable per run** — re-run ethos on the trimmed signature |
| `defs_reader` | 612 | **checkable** — text splicing, structural |
| `lean_meta`, `smt_meta` | 2,835 | **checkable** — round-trip, and cross-backend agreement |
| `desugar` | 1,347 | the semantic content; needs §1 |

Two thirds of the C++ is checkable rather than provable. None of this replaces
noesis — the entry is a fork about where the semantics *lives*, and validation
of an artifact says nothing about that. It is what the tree could do while the
fork is undecided, and none of it is wasted whichever way the fork goes.

## 6. Preparation, ordered

Cheapest first, each labelled with the ynoia entry or id it serves. None is
work anybody has promised.

**1. Write the preservation statement for each stage.** One page, precise, in
this tree. *desugar*: the relation of §2, stated with its quantifiers.
*model-smt*: a conservative extension — adds `$eo_model_sat` and changes nothing
an existing proof depends on. *lean-meta* / *smt-meta*: the emitted term denotes
what the Eunoia program denotes under the embedding. Zero code, and nothing
below is well-posed without it. Its most useful output is the statements that
turn out not to be writable yet — which is §1's question in operational form.
*Serves:* noesis, **open question 7**.

**2. Make the desugar differential a gate.** §2 ran it by hand; a
`tools/eoc/test/` entry beside `regress.py` would run it on every change, over
the whole of `tests/` rather than eighty files, and report the refusals as a
coverage number rather than as nine crashes nobody counts. *Serves:*
**elenchos**, **O6**. *Where:* this tree — the corpus and the binaries are both
here.

**3. Close `is_list_nil` in both directions, then verify it.** Part IV items 2
and 3, already scoped. Not for its own sake: it is the *template* for "a
hand-written predicate with a written-down intended meaning becomes a discharged
obligation", and a verified compiler performs that move everywhere. Doing it
once, end to end, prices the pattern. *Serves:* **O6**.

**4. Cross-backend agreement as an oracle.** One IR, two independent printers. A
closed Eunoia program evaluated by ethos, by `#eval` on the generated Lean, and
as a query on the generated `.smt2` must give one answer. Today cvc5
`--parse-only` and Lean's type checker catch ill-formed output and nothing
catches meaning. *Serves:* **elenchos** — this is its "semantics as the oracle",
with the independence question answered honestly rather than assumed.

**5. Prove `linear_patterns`.** 176 lines, spec is "the linearized program is
extensionally equal to the original", statable over the `eo.Term` embedding that
already exists. It answers the question that actually gates noesis: *is the
embedding good enough to state compiler theorems in?* Nobody knows, and this is
the cheapest way to find out. *Serves:* **noesis**, as its readiness probe.

**6. Stamp provenance on generated artifacts.** Every output carries the digests
of the `.eo`, of every `.eos`, and of the compiler revision that produced it.
Any theorem is about a specific artifact pair; today `tools/eoc/out/` is
gitignored and `regress.py` holds digests of one run, so there is no link from a
`Logos.lean` back to what produced it. Cheap now, miserable to retrofit.
*Serves:* noesis, **hermeneia**, and anything downstream that wants to name what
it is talking about.

**7. Write the honest end-to-end TCB ledger.** `proof_pipeline.md` reports the
TCB as 2,680 lines of Lean. That is the TCB of the *Lean theorem*, and correct
as such. The TCB of the *claim* also contains 5,430 C++, 2,026 Python, 1,551
Eunoia and 494 Lean of template. Writing the second one reorders every priority
after it. *Serves:* **O6**, **open question 2**. *Where:* this tree, in the
shape dokimasia already uses for cvc5 — its `TCB` facet asks the same question
about a different subject, and a ledger legible to that reader is worth more
than a second format.

**8. Say what each target's language brings.** Part IV item 8: one line per
target naming the operators it has without being told, checked against the
natives a run actually reaches. It is the only place left where a layer is
unchecked in *both* directions. Small, and it stops being optional the moment
`eo::native` opens the vocabulary. *Serves:* **O2**.

Items 1, 2 and 6 are useful under every arrangement in ynoia's table, which is
the argument for starting there rather than with the ones that are more
interesting.

## 7. What this does not settle

**Not argument 1.** Nothing here touches whether the SMT-facing artifact should
be `.eo`. Everything above assumes it stays and would be equally true if it did
not.

**Not the fork.** Noesis and iogos pull opposite ways on where the semantics is
defined, and §1's recommendation — make the Eunoia embedding normative — is
*compatible with both* and therefore settles neither. An embedding validated
against `src/` is what noesis would port and what iogos would need outside every
prover. That is a reason to do it before the fork is decided, not evidence about
which way to decide.

**Not the population question.** Validating the embedding demands Eunoia
fluency; noesis would demand Lean fluency. Neither removes the requirement.

**And not this tree's enthusiasm for its own work.** §4 argues that ethosEoc3
partly discharged somebody else's blocker, and the tree that did the work is not
the one to be trusted about how much. The measurement in §2 is the part of this
document that is checkable by running something, and it is the part to attack
first.
