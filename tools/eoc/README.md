# The Eunoia compiler

`ethos-eoc` takes a proof calculus written in Eunoia and compiles it: into a
proof checker for that calculus, and into the obligations that say the calculus
is sound.

It is the compiler behind **Logos**, the Lean development for the CPC proof
calculus. The Lean package Logos is built on is not written by hand; it is
generated from the calculus by this tool, and regenerated whenever the calculus
changes.

## Any calculus, several targets

Nothing in the compiler is specific to one calculus. A run names the signature
to compile and, separately, what its symbols mean, so a second calculus is a
second pair of those rather than a change here: the tests in this tree compile
`tests/Booleans-rules.eo`, the wrappers in [`cpc/`](cpc/) compile CPC, and the
semantics CPC is compiled under lives in the Logos repository rather than in
this one.

Whichever calculus it is, it compiles to each of these targets, from one
description of what its symbols mean:

| Target | What it produces | Command |
| --- | --- | --- |
| **Lean** | a proof checker for the calculus, its term language, and one lemma per proof rule | `driver.py lean` |
| **SMT-LIB** | a verification condition per proof rule; a solver that refutes it has shown the rule sound | `driver.py vc` |
| **SyGuS** | a synthesis query per proof rule, which searches for a counterexample to it | `driver.py vc --sygus` |

The two are independent, and that is the point of the tool: a target is a
backend rather than a restatement of the calculus, and a calculus is a
description rather than another compiler. What a symbol means is written once,
as configuration, and every target is compiled from it; a new theory, a new
proof rule or a new operator is added to the calculus and reaches every target
with no compiler change at all.

### What a symbol means is written in `.eos`, and this is its reference

**[`semantics/README.md`](semantics/README.md) is the reference for the
configuration language** -- the grammar, every entry with the attributes it
may carry, the four vocabularies a body may be written in and how one is cast
between them, what the compiler checks, worked examples, and what every
diagnostic means.

Almost all work on a calculus is an edit to one of those files rather than a
change to anything here, and a target is reached by writing configuration
rather than by writing a compiler, so that is the page to have open. The sets
are `tools/eoc/semantics/` for what a calculus and SMT-LIB mean, and the
`.eos` beside each stage under `plugins/` for what that stage is told.

`tools/eoc/driver.py` is the entrypoint for all of them, and exposes them as
one documented interface. See [Quick start](#quick-start) to run one, and
[`proof_pipeline.md`](../../proof_pipeline.md) for where this sits in the wider
cvc5 proof pipeline.

## What `ethos-eoc` is

`ethos-eoc` is the Eunoia binary built with the compiler plugins, one to a
stage:

- `desugar`
- `trim-defs`
- `model-smt`
- `smt-meta`
- `lean-meta`

The default `ethos` build does not include them: it checks proofs, and this one
compiles the calculus the proofs are written in. Build it with the two commands
under [Building `ethos-eoc`](#building-ethos-eoc).

`model-smt` gives every symbol of the signature its SMT-LIB semantics. A symbol
that instead has no semantics of its own is *eliminated* on the way to the
SMT-LIB term layer, i.e. it is defined in terms of the other symbols of the
signature. Such a reduction is written in the syntax of the signature itself,
as an ordinary `define` whose name is `$eo_reduce_` followed by the symbol it
reduces.

## The signatures written in the deep embedding

What a symbol means to the model is said by two files, and a run may name
either: the semantics of the input with `--semantics`, and the SMT-LIB
semantics it is written against with `--smt-semantics`.

```text
tools/eoc/out/smt_defs.eo   the SMT-LIB semantics, written in the embedding
tools/eoc/out/user_defs.eo  how the input's symbols transform into it
```

**Both are generated**, from the configuration under `tools/eoc/semantics`,
which `tools/eoc/sem_compile.py` compiles before any stage runs; neither is
checked in. What the options name is therefore the *central file of a
configuration set* rather than what it compiles to:

```text
python3 tools/eoc/driver.py lean --all \
  --semantics tools/eoc/semantics/development-cpc.eos \
  <cvc5>/proofs/eo/cpc/Cpc.eo
```

A file that is not a central file is taken to be a signature already written
out and is passed through, which is what lets one that has no configuration
still be given directly. See `tools/eoc/semantics/README.md` for what the
configuration is and the language it is written in.

A run compiles **one set of each role**, and the set an option names stands in
for the one the tool ships with rather than compiling beside it. Where a set
compiles to is said by its role and by nothing else, so the four generated
files have the names above whatever a run names and wherever the sets stand.

Only the `model-smt` stage reads them; no stage before it sees either. A symbol
the input declares that the file says nothing about is an error rather than a
term the model would silently say nothing about. The plugin ships with the
SMT-LIB semantics but with no signature of an input, so a run that names none
is an error once that stage runs.

The examples below leave `--semantics` out because the wrappers in
`tools/eoc/cpc` pass it, see `EOC_DEFAULT_SEMANTICS` in `common.sh`; the
driver on its own requires it.

Each is a sequence of blocks, one per symbol, opened by a `; -- X` line. For a
symbol X, `smt_defs.eo` gives the constructor `$emb_sm.X` and the macro
`$sm_X`, the cases X contributes to `$smtx_typeof` and to `$smtx_model_eval`
(as `$eoc_typeof_X` and `$eoc_eval_X`), and the auxiliary programs those cases
call. `user_defs.eo` gives `$eoc_transform_X`, the cases X contributes to
`$eo_to_smt`, and `$eoc_transform_type_X` for a type constructor.

What a block says to the compiler is named `$eoc_`, which is what tells it
apart from what the compiler emits: the case of an `$eoc_` program is spliced
into the aggregate its family names, so the name itself never reaches the
generated file. The exception is `$eoc_is_list_nil_X`, which the desugar stage
calls by name and which is therefore emitted as `$eo_is_list_nil_X`.

Which families there are is not something either side knows by name. The head
of each generated file declares them, one line to an aggregate:

```text
; $eoc-aggregate $smtx_typeof $eoc_typeof_ $SMT_TYPEOF_CASES$
; $eoc-aggregate $eo_is_list_nil_ $eoc_is_list_nil_ $EO_DESUGAR_AUX$ whole
```

which says the aggregate a case joins, the name the case is written under, and
the marker of `plugins/model_smt/model_smt.eo` the stage writes them at; the
longest name a program begins with is the aggregate it belongs to, and `whole`
is the exception above. The lines are compiled from
`plugins/model_smt/model_smt.eos`, which is where an aggregate is to be changed
or added, and the stage reads them rather than knowing any of it, so adding one
asks nothing of `ethos-eoc`. See `semantics/README.md`.

A block may also be of a helper rather than of a symbol, in which case the
`; -- X` line names the helper itself, e.g. `; -- $smtx_typeof_bv_op_2` for the
typing of a bit-vector operator whose two arguments must be of one width. Such
a block is taken only when a block that is kept names it, so a signature with
no bit-vectors in it compiles to a model that has never heard of them.

A helper belongs in the signature when only theory operators call it. That is
the whole of what a signature may hold beside its symbols: a set says what a
theory **does** and never what the embedding **is**, so it writes programs and
never a declaration, and a form that is neither is refused rather than carried
over as the text it is; see `semantics/README.md`. The programs over a map --
looking an entry up, typing one, saying whether one is written the one way --
are therefore written in the configuration beside the sort they belong to,
while the `$smt_Map` they are written over is declared in
`plugins/model_smt/model_smt.eo` with the rest of the embedding.

What remains in `plugins/model_smt/model_smt.eo` is what says what the
embedding is, and what no theory is what asks for:

- the term, type and value languages the file declares itself -- the shapes a
  value is built over among them -- and the aggregates written over them;
- the datatypes, which an input *declares* rather than a theory naming, and the
  types the embedding keeps for what an input declares -- `USort`, `FunType`,
  `DtcAppType`, `TypeRef`;
- the binders, an application, and the programs over types that everything else
  is written against -- well-foundedness, boundedness and the default of a
  type.

Every helper a signature writes is emitted together, before the first aggregate
whose cases may call one; they are one stream because they are one dependency
graph, and what orders them is the signature itself, which writes a program
after the ones it calls. See `$SMT_HELPER_PROGS$` in the template.

The stage takes the blocks of the symbols the input declares, together with
every block those name, and puts what each says where it belongs; it knows
nothing about any symbol itself. A block is copied as *text*, which is what
keeps the definitions of the embedding it names, e.g. `$vsm_bool`, from being
expanded on the way. See `plugins/model_smt/defs_reader.h`.

Both files are ordered so that a symbol follows the ones its cases name, which
is why neither needs a forward declaration. Adding, changing or removing a
symbol is a change to one block and does not require rebuilding `ethos-eoc`.

A block may name a symbol of the *input* rather than of the embedding, as the
transformation of `@quantifiers_skolemize` names `forall` in the pattern it
matches. Trimming a signature to one proof rule has to keep such a symbol, so
the driver reads those dependencies off the blocks and tells `trim-defs`; see
`Pipeline.defs_depends` in `tools/eoc/driver.py`.

A block may also say that the compilation has no place for what it is of at
all: SMT-LIB gives a proof-level binder no meaning, so `lambda` and everything
that reduces an application of one are left out rather than modelled. A block
says so with directives of the following forms:

```lisp
(echo "eoc-exclude symbol lambda")
(echo "eoc-exclude method $beta_reduce")
(echo "eoc-exclude rule beta-reduce")
```

The configuration writes `:exclude` on the symbol, the method or the rule
itself -- a method with `define-method` and a rule with `define-rule` -- and the
compiler puts the directive back, the kind being what the form that declared it
says one is; see `semantics/README.md`.

`Pipeline.defs_excludes` collects them and gives them to the desugar stage,
which is what drops what they name; a rule among them is also left out of
`--all-rules`, since there is nothing to verify about it. The names are matched
literally: the compiler neither checks that a name exists nor computes a
dependency closure, so every declaration that goes with an omitted one says so
for itself.

## Why the generated Lean terminates

Lean has to be told why a recursive definition terminates whenever it cannot
see this for itself, and no measure the compiler could guess would do for the
programs that need one. So the clause is stated as the Lean text it is, under
`:lean` in the configuration set of the signature the program is of (see
`semantics/README.md`), and the `lean-meta` stage appends it to the definition
of the program it names:

```text
tools/eoc/out/smt_termination.lean   the programs of the deep embedding, which
                                     every input is compiled through; read by
                                     the stage itself
tools/eoc/out/user_termination.lean  the programs of the input signature,
                                     passed to the stage by the driver
```

Both are generated by `sem_compile.py`, so what is to be changed is the
`:lean` attribute of the set. A block of one runs from a line naming one or
more programs, written `-- $name ...`, to the next comment line, and what lies
between is the clause. An input whose programs all recurse structurally needs
no clauses of its own; a signature given already written out rather than as a
configuration names its clauses with `--lean-config`. Without clauses the
generated Lean simply carries none for those programs, which Lean will reject
if one was needed.

A clause may not name the native layer, which the compiler checks. It is text
the stage appends rather than text the stage printed, so naming a definition
of the layer there asks for nothing: the definition may have been dropped as
unreached, see "The native layer" below. Every native type abbreviates a Lean
type, which is what a measure writes instead.

## The natives of the embedding

What a signature written in the embedding may call that no compiler writes is
declared in `plugins/desugar/natives.eos`, one entry to a native:

```lisp
(declare-native binary_and ((w <numeral>) (n1 <numeral>) (n2 <numeral>)))
(declare-native z_zero () :op "0")
```

`sem_compile.py` compiles that set into `tools/eoc/out/native_defs.eo`, the
declarations the desugar layer carries, which stand where the
`(include "native_defs.eo")` of `plugins/desugar/native_embed.eo` names them.
Nothing writes one by hand: a declaration says only the name, what each
argument is and the operator it forwards to, and the set says all three.

### What one native is called

A native is written under one name and comes out under several, one per place
it reaches. Taking `zplus`, which the embedding calls where a signature adds
two numerals:

| Where | Spelling | `zplus` |
| --- | --- | --- |
| `desugar/natives.eos`, which declares it | the name | `zplus` |
| desugared Eunoia, and the `eo-meta` output | `$native_` and the name | `$native_zplus` |
| `lean_meta/lean.eos`, `smt_meta/smt-vc.eos`, which implement it | the name it forwards to, i.e. `:op` where it has one | `zplus` |
| generated Lean | `native_` and that | `native_zplus` |
| generated SMT-LIB | that, unchanged | `zplus` |

The `eo-meta` backend is the one that adds no spelling of its own: what it
writes is Eunoia, and Eunoia already calls it `$native_zplus`.

A definition a Lean block writes for itself, rather than the one it declares,
is named `impl_native_` instead, which is what says it is private to that
block: `impl_native_int_log_rec` is nothing a signature may reach.

Where a name is spelled is settled in `LAYERS` in `tools/eoc/sem_compile.py`,
one entry to a backend.

What is left in `native_embed.eo` is what the embedding *is* rather than what
it calls, and nothing else: the `$native_apply_*`, `$native_type_*` and
`$native_embed_*` constructors, declared and never written over. It holds no
definition at all.

Everything else the set says. It declares the primitive types the natives are
written over as well as the natives themselves -- `<numeral>` is what a
configuration calls what a backend calls `Int` -- so that a set says the kind
of thing it means rather than the sort some target happens to have. Three of
the six name no SMT-LIB sort at all.

A native that forwards to nothing says what it *is* instead, under `:is`,
written in the vocabulary every body of a configuration is written in:

```lisp
(declare-native z_dec ((x1 <numeral>)) :is ("zplus" x1 "z_neg_one"))
```

What a native that forwards to an operator **does** is a separate thing, said
by each backend in a native layer of its own; see below. The two are apart
because neither implies the other: a backend may define what the embedding
never calls, and the embedding may call what a backend gets from its own
language. A native written with `:is` needs neither, since what it is has been
said once already.

## The native layer

What a backend generates is written against a layer of definitions that gives
the deep embedding its arithmetic, its strings, its regular expressions and
the rest -- what the generated text is allowed to call and no compiler writes.
Each backend has one, and the two are the same thing said twice:

| backend | set | compiles to | read by |
| --- | --- | --- | --- |
| Lean | `plugins/lean_meta/lean.eos` | `tools/eoc/out/lean_native.lean` | the `lean-meta` stage |
| SMT-LIB | `plugins/smt_meta/smt-vc.eos` | `tools/eoc/out/smt_vc_native.smt2` | the `smt-meta` stage |

### What the backend writes for itself

The inductive a datatype of the embedding prints as, and the ordering key
beside it, are generated: a constructor the target declares reaches the backend
like any other, and the backend gives an inductive to whatever it is handed,
named as the type the constructor returns. Nine datatypes come out that way --
the term, the type and the value, and the map, the sequence, the regular
language and the three a datatype declaration is made of.

A datatype's constructors are therefore said once, in
`semantics/smt.eos`, and their order there is what the tags of its ordering key
are taken from.

### What a layer owes the embedding

The embedding declares 66 natives. Which of them a layer *must* implement is
not "all of them", and the rule has three parts:

| a native that | the layer owes it | how many |
| --- | --- | --: |
| says `:is`, being written over the others | nothing -- what it is was said once | 7 |
| forwards to a **literal**, as `z_zero` does to `0` | nothing -- a literal is itself in every target | 12 |
| forwards to an operator the **target language already has**, as `and` does in SMT-LIB | nothing | varies |
| forwards to anything else | a definition | the rest |

Where the layers stand today, counting the 47 primitives that do not forward to
a literal:

| layer | implements | of |
| --- | --: | --: |
| `lean_meta/lean.eos` | 47 | 47 |
| `smt_meta/smt-vc.eos` | 34 | 47 |
| `eo_meta/eo.eos` | 28 | 47 |

**The third row of the first table is the hole.** Nothing anywhere says which
operators a target already has, so nothing can tell a native SMT-LIB gets for
free -- `and`, `or`, `not`, `ite`, `to_real` -- from one that is simply
missing. The thirteen `smt-vc.eos` does not implement are all of the first
kind, and the nineteen `eo.eos` does not are mostly not: a native with no
`:eo-impl` falls back to an opaque `$native_apply_N`, so the eo-meta output
names an uninterpreted operator rather than failing.

So the coherence of a layer is **unchecked in both directions**: a native no
layer implements and no language has surfaces as a Lean or cvc5 error two
tools downstream, and a layer entry for a native the embedding no longer
declares is dead text nothing reports. See "What is not checked for you" in
[`docs/README.md`](../../docs/README.md).

What would close it is one line per target saying what its language brings --
the operators it has without being told -- against which the compiler could
check every native the compiled signature actually reaches. That is a smaller
question than it looks, since only the natives a *run* reaches matter, and the
run already knows which those are.

**A layer is a configuration set**, which `tools/eoc/sem_compile.py` compiles;
one entry is one definition, under the attribute that says which language it
is written in:

```lisp
(define-native-method str_to_upper
  :lean-impl "def impl_native_char_to_upper (c : native_Char) : native_Char :=
  if 97 <= c && c <= 122 then c - 32 else c

def native_str_to_upper : native_String -> native_String
  | s => s.map impl_native_char_to_upper")

(define-native-method int.to_nat
  :smt-impl "(declare-fun int.to_nat (Int) Nat)
(assert (! (forall ((x Int))
  (! (= (int.to_nat x) (ite (<= x 0) nat.zero (nat.succ (int.to_nat (- x 1)))))
  :pattern ((int.to_nat x))))
  :named smtx.int.to_nat.def))")
```

The name is spelled the way the embedding names it: the Lean backend puts the
`native_` back, and the SMT-LIB one forwards the name as it stands, which is
why `int.to_nat` is written under that name there and under `int_to_nat` in
the Lean set. Whatever else an entry defines has no name here and so is
private to it, which `impl_native_` rather than `native_` is what says on the
Lean side. A definition that is axiomatised rather than defined -- a
`declare-fun` and the `assert` that says what it is -- is one entry, since
neither half is of any use without the other.

Everything below holds of both layers: what a stage is given is the same file
in two languages, and the code that reads it is one class, `ethos::NativeLayer`
in `plugins/native_layer.cpp`.

### Where a definition comes out

**Only what the compilation of an input reaches is emitted.** Most of a layer
is dead for any one input: a signature with no strings in it has no use for
the regular-expression matcher, and one of Booleans alone has none for
arithmetic. The Lean layer is 116 definitions and 660 lines, of which a
published `CpcMini` carries 46 and the full CPC package all but two; the
SMT-LIB layer is 67, of which the verification condition of `symm` carries 16
-- and what it drops includes nine quantified axioms, which is work the solver
does not do.

A backend has one place per module its generated text is read in, each taking
what comes out there as an ordinary replacement:

| backend | place | tag in | scope |
| --- | --- | --- | --- |
| Lean | `SmtEval.lean` | `lean_meta_smt_eval.lean` | `SmtEval`, which every module sees |
| Lean | `Logos.lean` | `lean_meta_checker.lean` | `Eo`, the Eunoia terms and what is written over them |
| Lean | `SmtModel.lean` | `lean_meta_smt_model.lean` | `Smtm`, the SMT-LIB value embedding |
| SMT-LIB | above the datatypes | `smt_meta.smt2` | `Vc`, where SMT-LIB alone is in scope |
| SMT-LIB | below the datatypes | `smt_meta.smt2` | `Embed`, where the embedding is declared |

Which of them a block comes out in is the demand for it: the module that names
it, the one they share when two do -- which is the scope every module sees --
and the one module that can hold it when its text names what only that module
declares. A block named by a block is named wherever that one comes out, so
the demand is closed over what each calls.

Neither of the two things this is read off is the generated text:

- **What a block names** is read by the compiler, off the block itself, and
  written on the line that opens it: the scope it cannot be written above, and
  the rest of the layer it calls. See `lean_needs`, `vc_needs` and
  `native_deps` in `tools/eoc/sem_compile.py`. Reading it there rather than
  beside the definition is what keeps it from drifting: an annotation can, and
  the text cannot drift from itself.
- **What an input names** is what the stage wrote: a name of the layer reaches
  generated text only by being printed into it, so the stage notes each as it
  prints it, against the scope the text it is printing comes out in. See
  `NativeLayer::use`, and `getEmbedName` in either stage for where a name is
  printed.

What no input reaches is what the resources of a stage name themselves --
`native_ite` in the term ITE of `lean_meta_checker.lean`, `native_Bool` in the
equality of `lean_meta_checker_term.lean`. Such a definition says `:keep` in
its set and comes out in the scope every module sees, which is what every
resource that names one can see. A resource that names one and does not say
so gets generated text naming a definition that was never written, which
**Lean, or cvc5 reading the verification condition, is what reports**.

### `eo::hash` has no Lean

EO leaves what `eo::hash` returns underconstrained, so a signature that
reasons through it says nothing this backend could prove; the layer used to
answer with a stub returning `0`, which is a claim about hash the signature
never made, so the layer defines no `native_thash`.

The `lean-meta` stage therefore refuses to print `$eo_hash`, the program of
the embedding that would call it, the way it refuses `$eo_ite`; see
`LeanMetaReduce::finalizeProgram`. A signature that uses hash gets generated
Lean naming a definition that was never written, and **Lean is what reports
it** -- the stage checks nothing further, since the generated file is not what
says whether a name exists. The other backends are unaffected: `$native_thash`
reaches SMT-LIB and SyGuS as the uninterpreted function it is.

## Building `ethos-eoc`

`ethos-eoc` is built by the standalone CMake project in `plugins/`, which
compiles the ethos core sources together with the plugins. The main ethos
build is unaffected. From the repository root:

```bash
cmake -S plugins -B build-eoc
cmake --build build-eoc --target ethos-eoc -j4
```

Pass `-DCMAKE_BUILD_TYPE=Debug` to the configure step for a debug build with
assertions and tracing. The driver configures the build directory
automatically if it does not exist yet.

`--build-dir` defaults to the current working directory, so pass it explicitly
whenever you invoke the driver from somewhere other than the build tree. The
examples below all use `build-eoc`.

## Checking a change left the output alone

```bash
python3 tools/eoc/test/regress.py            # say whether the bytes moved
python3 tools/eoc/test/regress.py --update   # take this run as what is written
```

The compiler is refactored more often than it is extended, and what a
refactor has to be is output-preserving. `regress.py` compiles a signature of
this tree, `tests/Booleans-rules.eo`, for one rule, and compares the digest of
every file the run leaves behind -- stage files and published artifacts alike
-- with what is checked in beside it. A run that changed something says which
files it changed. CI runs it on every push.

What is checked in is the digest of each file rather than the file, since the
tree checks in no generated artifact at all; see the `tools/eoc/out/` line of
`.gitignore`. The digests are of what the pipeline wrote *under these
semantics*, so a change to `semantics/smt.eos` or to
`semantics/development-cpc.eos` moves them, and rightly: `--update` is how a
run that meant to change the model says so, and the diff of `expected.txt`
then shows how much of the output that change reached.

The whole-signature path is not covered. No signature in this tree is one the
semantics the tool ships with covers entirely, so `lean --all` over one stops
at the first symbol the semantics says nothing about; what covers it is a
calculus of another tree, e.g. the CPC wrappers in `tools/eoc/cpc`.

`python3 tools/eoc/sem_compile.py --check` is the other half: it says the
generated signatures hold what compiling the configuration writes, and that
each block of one stands after the blocks it names.

## One important path rule

The driver resolves input paths relative to the directory where you invoke
`python3 tools/eoc/driver.py`, not relative to the build directory.

For example, from the repository root:

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc tests/Booleans-rules.eo and_intro
```

The input path `tests/Booleans-rules.eo` is interpreted relative to the
repository root. The driver writes its EO stage files and final published
outputs under `tools/eoc/out` by default.

## What a run prints

Every tool of the pipeline says what it is doing the same way, which matters
because the checks that run this compiler live in other repositories -- logos
and cvc5 -- and read its output there. One step of a run is a line under
`-- `, what a step is made of is indented two spaces further, and a path is
written from the root of the repository, so that a log reads the same whichever
machine wrote it:

```text
-- Compiling semantics under tools/eoc/semantics
--   smt.eos             -> tools/eoc/out/smt_defs.eo (219 blocks)
--   smt.eos             -> tools/eoc/out/smt_termination.lean (12 clauses, unchanged)
--     132 symbols, 5 literals, 9 types, 14 values, 12 methods, 67 programs
--   development-cpc.eos -> tools/eoc/out/user_defs.eo (194 blocks, unchanged)
-- Generating Lean for /home/me/cvc5/proofs/eo/cpc/Cpc.eo
--   [1/4] desugar   -> tools/eoc/out/lean-cpc-desugar.eo
--   [2/4] model-smt -> tools/eoc/out/lean-cpc-final.eo
--   [3/4] parse        tools/eoc/out/lean-cpc-final.eo
--   [4/4] lean      -> tools/eoc/out/lean
-- Installing the generated Lean of tools/eoc/out/lean into /home/me/logos/Cpc
--   Logos.lean         -> Cpc/Logos.lean
--   Rules/*.lean       -> Cpc/Proofs/Rules/ (591 copied, 0 preserved)
```

A path outside the repository -- the signature of a calculus, the tree the Lean
is installed into -- is written as it stands, since nothing else would name it.

What went wrong is *not* a step. It goes to stderr as `error: ...`, which is
what a caller's CI looks for, and the run exits non-zero; a run that carried on
regardless says so as `warning: ...`. Anything meant to be read by a program
rather than a person -- the rule names of `list-rules` -- is written plainly to
stdout with no prefix at all.

The style is defined in one place per language: `tools/eoc/report.py` for the
tools, and `eoc_step`, `eoc_item`, `eoc_error` in `tools/eoc/cpc/common.sh` for
the scripts that call them.

## Output layout

The driver uses two output trees:

- `tools/eoc/out/` for stage EO files and final published outputs, unless
  overridden with `--final-out-dir` or `EOC_FINAL_OUT_DIR`, and for what the
  configuration compiles to, which stands there whatever a run overrides and is
  not checked in
- `<build-dir>/out/plugins/` for plugin-private generated files consumed by the
  driver

Published and stage files:

```text
tools/eoc/out/
  smt_defs.eo               what the configuration compiles to, see
  user_defs.eo              tools/eoc/semantics/README.md
  smt_termination.lean
  user_termination.lean
  lean_native.lean          the native layer of each backend, see above
  smt_vc_native.smt2
  trim-*.eo
  trim-d-*.eo
  vcm-def-*.eo
  vcmt-def-*.eo
  desugar.eo
  lean-*-trim.eo
  lean-*-desugar.eo
  lean-*-defs.eo
  lean-*-final.eo
  trim_defs/trim_gen.eo
  vc/final-*.smt2
  sygus/final-*.sy
  lean/
    Logos.lean
    LogosTerm.lean
    Parser.lean
    SmtEval.lean
    SmtModelDefs.lean
    SmtValueOrder.lean
    SmtModel.lean
    Spec.lean
    Proofs/
      RuleLemmas.lean
      Rules/
        <Rule>.lean
```

`out/lean/` is the package the files are installed into, not a Lean package
that builds on its own: the generated modules import `<Calc>.Proofs.CheckerCore`
and `<Calc>.Proofs.RuleSupport.Support`, which the compiler never writes and
which belong to that package. The proof-side modules stand under `Proofs/`,
which is what the `import <Calc>.Proofs.Rules.<Rule>` lines `RuleLemmas.lean`
carries name; every other file stands at the root, where its name already is
its import. Installing is therefore a copy of the tree, and a file added to
`LEAN_OUTPUTS` in `tools/eoc/driver.py` arrives with no change to the install
wrappers.

`<Calc>` is what `--calc-name` says, which is the name of the package the run
installs into; a run that names none calls the calculus after its input file,
up to the first dot.

A published module is read by whoever reads the package, so what the resource
it was rendered from says to whoever *edits* the resource -- what a tag stands
for, why something is written there rather than where it belongs -- is written
as a **note**, a comment whose text opens with a `$`: `-- $` where the resource
is Lean and `; $` where it is SMT-LIB. A note is dropped when the resource is
rendered, so it never reaches the package; see `dropResourceNotes` in
`plugins/utils.cpp`. Everything else a resource writes is published as it
stands, and is written to the reader of the package.

Plugin-private files:

```text
<build-dir>/out/plugins/
  desugar/
  lean_meta/
  model_smt/
  smt_meta/
  trim_defs/
```

## Quick start

Generate one VC:

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc tests/Booleans-rules.eo and_intro
```

Generate one SyGuS query:

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc --sygus tests/Booleans-rules.eo and_intro
```

Generate Lean for selected rules:

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc tests/Booleans-rules.eo and_intro contra
```

Generate Lean for the whole signature:

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc --all <cvc5>/proofs/eo/cpc/Cpc.eo
```

A declaration the signature of the input leaves out of the compilation is
dropped by this run without anything being said on the command line; see "The
signatures written in the deep embedding" above.

List all rules declared by a signature and its includes:

```bash
python3 tools/eoc/driver.py list-rules <cvc5>/proofs/eo/cpc/Cpc.eo
```

Run every discovered rule through the VC pipeline:

```bash
python3 tools/eoc/driver.py batch --build-dir build-eoc vc <cvc5>/proofs/eo/cpc/Cpc.eo --all-rules --clean
```

Run every discovered rule through the SyGuS pipeline:

```bash
python3 tools/eoc/driver.py batch --build-dir build-eoc sygus <cvc5>/proofs/eo/cpc/Cpc.eo --all-rules --clean
```

## Command reference

### `vc`

Generate a single SMT2 VC for one rule.

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc INPUT RULE
```

Useful options:

- `--sygus`: generate a SyGuS query instead of SMT2
- `--skip-cvc5`: skip parse checks with `cvc5`
- `--solve`: run `cvc5` on the generated VC or SyGuS file after optional parse checks
- `--solve-args "ARGS"`: shell-style string of extra options passed to `cvc5` during `--solve`
- `--no-build`: do not rebuild `ethos-eoc` first
- `--cvc5 /path/to/cvc5`: override the solver used for parse checks

### `batch`

Run many rules through the same pipeline.

```bash
python3 tools/eoc/driver.py batch --build-dir build-eoc vc INPUT RULE1 RULE2 RULE3
```

Useful options:

- `--all-rules`: discover all `(declare-rule ...)` entries recursively
- `--rules-file FILE`: read one rule name per line from a file
- `--clean`: remove old files from `out/vc` or `out/sygus` first
- `--keep-going`: continue after failures and report all failed rules
- `--skip-cvc5`
- `--solve`
- `--solve-args "ARGS"`
- `--no-build`

### `lean`

Generate Lean output either for selected rules or for the full signature.

Selected rules:

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc INPUT RULE1 RULE2
```

Whole signature:

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc --all INPUT
```

Pass `--no-parser` to omit the signature-specific `Parser.lean` artifact while
still generating the remaining Lean modules and per-rule files.

Pass `--calc-name NAME` to say what the generated Lean calls the calculus,
which is the name of the package the run installs into, e.g. `Cpc`. Naming it
here is what makes the imports of the published tree right where they are
written; a run that names none calls the calculus after its input file, up to
the first dot.

Pass `--lean-config FILE` to name the termination clauses of the input's own
programs where the input was given already written out rather than as a
configuration set; see "Why the generated Lean terminates" above.

The generated modules carry only the `native_` definitions the input reaches,
so the same signature compiled for fewer rules publishes a smaller native
layer; see "The native layer" above.

Generated files are written to `tools/eoc/out/lean/` by default, including
per-rule files in `tools/eoc/out/lean/Proofs/Rules/`. The tree is written
afresh each run, so it holds the whole of what that run compiled and nothing
else. `Parser.lean` is the minimal
calculus-specific instantiation of the generic Logos proof parser: it contains
only the generated operator/rule tables, indexed-operator constructors, and
surface desugaring configuration.

The operator tables also cover the identifiers the input introduces with
`define`. Eunoia inlines a definition, so it has no counterpart in the compiled
signature, but a proof may still use it. The desugar stage therefore re-emits
each definition it can under the name `$parse_<name>`, which the later stages
reparse and otherwise ignore. By convention a definition whose own name begins
with `$` is a helper of the signature and is not preserved, since a proof never
mentions one. A preserved definition contributes to the parser only, never to a
verification condition or to the generated proof checker. A definition that
takes arguments becomes a macro of the parser, and one that takes none becomes a
nullary operator, or an alias of the operator it names so that it inherits its
indices and argument-list attribute.

### `desugar`

Generate the desugared EO form of an input.

```bash
python3 tools/eoc/driver.py desugar --build-dir build-eoc INPUT
```

Output:

```text
tools/eoc/out/desugar.eo
```

### `trim-defs`

Run only the trim stage.

```bash
python3 tools/eoc/driver.py trim-defs --build-dir build-eoc INPUT TARGET1 TARGET2
```

Output:

```text
tools/eoc/out/trim_defs/trim_gen.eo
```

### `list-rules`

Print discovered rules without running the pipeline.

```bash
python3 tools/eoc/driver.py list-rules INPUT
```

This walks `include` chains and preserves declaration order.

## Common workflows

### Generate a VC for one rule

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc INPUT RULE
```

### Generate VCs for every rule

```bash
python3 tools/eoc/driver.py batch --build-dir build-eoc vc INPUT --all-rules --clean
python3 tools/eoc/driver.py batch --build-dir build-eoc sygus INPUT --all-rules --clean
```

### Generate Lean and then copy files elsewhere

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc --all INPUT
ls tools/eoc/out/lean
```

`tools/eoc/cpc/install_logos` and `tools/eoc/cpc/install_logos_mini` run the
`lean` pipeline through `driver.py` under the name of the package they install
into, then copy the tree at `tools/eoc/out/lean` into a downstream Logos tree:
that tree already has the layout of the package, so installing adds nothing to
what publishing said. A rule file already in the package is kept, since a
hand-written proof may stand beside the generated one. The destinations are the
ones named in [`cpc/README.md`](cpc/README.md), each overridable with an
environment variable.

### Manually inspect or debug intermediate files

The driver writes the staged EO files into `tools/eoc/out/`. You can pass those
directly to `ethos-eoc` if you want to debug a later stage manually.

Examples:

```bash
build-eoc/ethos-eoc tools/eoc/out/trim-d-booleans-rules.eo
build-eoc/ethos-eoc --plugin.smt-meta tools/eoc/out/vcmt-def-booleans-rules.eo
build-eoc/ethos-eoc --plugin.smt-meta-sygus tools/eoc/out/vcmt-def-booleans-rules.eo
build-eoc/ethos-eoc tools/eoc/out/lean-booleans-rules-final.eo
build-eoc/ethos-eoc --plugin.lean-meta tools/eoc/out/lean-booleans-rules-final.eo
```

## Solver configuration

By default, parse checks use:

1. `--cvc5 /path/to/cvc5`, if passed
2. `$CVC5`, if set
3. `cvc5` on `PATH`

If none of those resolve, either pass `--skip-cvc5` or set `CVC5`.

## Troubleshooting

### `Couldn't open file: ...`

Check which directory you ran the driver from. Input paths are resolved
relative to the current shell directory, not to `--build-dir`.

### `cvc5 executable not found`

Either:

- pass `--skip-cvc5`
- pass `--cvc5 /path/to/cvc5`
- export `CVC5=/path/to/cvc5`

### I want to inspect the generated artifacts directly

Look in `tools/eoc/out/` for both the staged EO artifacts and the final
published outputs. The plugin-private generated files remain under
`<build-dir>/out/plugins/`.
