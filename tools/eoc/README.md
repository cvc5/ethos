# EOC Workflow

`tools/eoc/driver.py` is the canonical entrypoint for the optional
`ethos-eoc` workflow, which it exposes as one documented interface.

## What `ethos-eoc` is for

`ethos-eoc` is the optional Eunoia compiler target that drives the
non-standard EOC plugins:

- `desugar`
- `trim-defs`
- `model-smt`
- `smt-meta`
- `lean-meta`

The default `ethos` build does not include these plugins. Use `ethos-eoc`
only when you want the Eunoia-to-SMT2 or Eunoia-to-Lean pipeline.

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

A clause may not name the native layer, which the compiler checks. It is
appended to a generated definition rather than written into a resource, so it
is not one of the blocks that layer is trimmed by and a name it gave would
keep nothing alive; see "Trimming the native layer" above. Every native type
abbreviates a Lean type, which is what a measure writes instead.

## Trimming the native layer

The Lean the compiler generates is written against a layer of definitions
named `native_`, which is what gives the deep embedding its arithmetic, its
strings, its regular-expression matcher and the rest. That layer is written
once for every signature there is, so most of it is dead for any one input: a
signature of Booleans alone has no use for the matcher, and one with no
bit-vectors has none for `native_binary_concat`. The `lean-meta` stage
therefore emits only the part of it the compilation of the input reaches.

**The layer is a configuration set**, `plugins/lean_meta/lean.eos`, which
`tools/eoc/sem_compile.py` compiles to `tools/eoc/out/lean_native.lean`; that
is the file the stage reads. One entry is one definition:

```lisp
(define-native-method str_to_upper
  :needs SmtEval
  :lean-impl "def impl_native_char_to_upper (c : native_Char) : native_Char :=
  if 97 <= c && c <= 122 then c - 32 else c

def native_str_to_upper : native_String -> native_String
  | s => s.map impl_native_char_to_upper")
```

The entry names the native **the way a set names one**, without the prefix the
embedding gives it: `str_to_upper` here is what `"str_to_upper"` names in a
set, and the compiler answers that with `native_str_to_upper`. The Lean the
entry is defines the prefixed name, since that is what the generated text
calls.

**Whatever else the `:lean-impl` defines is private to that entry**, and is
called `impl_native_` rather than `native_` to say so. The prefix is the whole
of the rule: no eoc reference can spell one, since the compiler only ever
answers with `native_X`, and the entry that writes it is free to change it
without asking what a signature relied on. Such a definition has no name in
the set either -- only the entry it stands in does -- so it is private twice
over: `impl_native_char_to_upper` above is text of the one entry that has any
use for it. Where several entries share a helper it is a `native_` entry of
its own instead, which is what the regular-expression matcher does: a set
names `"str_in_re"`, and the derivative step underneath it is
`native_re_deriv`, reached by seven of them.

What each entry compiles to is a *block* of the generated file, opened by a
`-- $native` line naming what it defines. Once every module has been written,
a block is kept when the generated text, or a block already kept, names it,
and dropped otherwise. Comments and string literals are not read, so a
definition named only in prose is not thereby kept alive. A `native_`
definition that its own block does not name is an error rather than one
quietly emitted for every input; an `impl_native_` one is not, since the block
it stands in is what it belongs to.

The layer is for what the embedding is written *over*, not for what is written
*about a model*: the model, its lookups and the quantifier evaluators stand in
`plugins/lean_meta/lean_meta_smt_model.lean`, and what decides equality of a
term, a type or a value stands beside the type it decides over. Those are
written in the templates as ordinary Lean and are emitted whatever an input
reaches, since the module they stand in is written for every one.

### Where a definition comes out

The entries are one set rather than text of the modules they end up in, so
that a definition is written once whichever of the generated modules turns out
to want it. Where a block comes out is the demand for it: a definition that
more than one module reaches is written into what they share, and one that a
single module reaches is written into that module.

What a module has in scope is what bounds this, since the layer is written
across more than one namespace. Each entry says how much it needs with
`:needs`, and the compiled file opens a section per scope:

```lean
-- $native-needs SmtEval
-- $native-needs Smtm
```

`SmtEval` is what a block that is Lean and nothing else needs, `Eo` what a
block over the Eunoia term embedding needs, and `Smtm` what a block over the
SMT-LIB value embedding needs. A file that is the home of a scope says so, and
the blocks that come out in it are written where it says:

```lean
-- $native-place Smtm
```

A file that is not the home of a scope but has one in scope says that instead,
which is what makes it a module a block of that scope can be written for:

```lean
-- $native-sees Eo Smtm
```

`SmtEval` is in scope everywhere and is not one a file has to name. A block is
written into the narrowest home that both has what the block needs in scope
and is seen by every file that reaches it; `SmtEval` is seen by all of them,
so a block that needs nothing always has a home. The result is that
`native_zneg`, which is Lean arithmetic and nothing more, is written into
`SmtEval.lean` for a signature whose model semantics negates and into
`Logos.lean` for one where only the checker does.

A block the file it stands in has to be read with is left in that file rather
than moved to the library, and is only kept or dropped. The definitions inside
`SmtModel.lean`'s `mutual ... end` are the ones this is of: they are mutually
recursive with the generated evaluator, so their place is that block and not
a library section.

### Roots

Some of the layer is called by the package the published tree is installed
into rather than by anything the compiler writes, and that side is not visible
here. Such a definition is declared a root, which keeps it whatever the
compilation reaches:

```lean
-- $native-root native_string_lit
```

The roots are written next to the definitions they are of, with the reason.
There are two today: `native_string_lit`, which a proof written against the
published tree names its strings with, and the reference lists, which the
translation proofs of the destination package use. A definition the *input*
signature reaches needs no root, since the closure finds it: `eo::cmp`
desugars to `$native_tcmp`, so a signature that uses it keeps that one on its
own.

`eo::hash` has no Lean at all. EO leaves what it returns underconstrained, so
a signature that reasons through it says nothing this backend could prove; the
layer used to answer with a stub returning `0`, which is a claim about hash
the signature never made, so the layer defines no `native_thash`.

The `lean-meta` stage therefore refuses to print `$eo_hash`, the program of the
embedding that would call it, the way it refuses `$eo_ite`; see
`LeanMetaReduce::finalizeProgram`. A signature with no use for hash never
misses it, since nothing names the definition. One that *does* use hash gets
generated Lean naming a definition that was never written, and **Lean is what
reports it** -- the stage checks nothing further, since the generated file is
not what says whether a name exists. The other backends are unaffected:
`$native_thash` reaches SMT-LIB and SyGuS as the uninterpreted function it is.

Adding a root is how to fix a downstream build that a trimmed tree broke. To
see what was dropped, run the stage with the whole layer emitted:

```bash
build-eoc/ethos-eoc --plugin.lean-meta --no-trim-natives tools/eoc/out/lean-cpc-final.eo
```

See `LeanMetaReduce::placeNativeDefs` in
`plugins/lean_meta/lean_meta_reduce.cpp`. The blocks live in
`lean_meta_native.lean`, apart from the ones `lean_meta_smt_model.lean` has to
be read with; the other Lean resources define none, and say only what they see
and where they are the home of a scope.

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
    RuleLemmas.lean
    Rules/
      <Rule>.lean
```

`out/lean/` is what a run publishes, not a Lean package that builds on its own:
the generated modules import `<Calc>.Proofs.CheckerCore` and
`<Calc>.Proofs.RuleSupport.Support`, which the compiler never writes and which
belong to the package the files are installed into. That package holds the
proof-side modules under `Proofs/`, and the published tree is it with that one
component dropped, uniformly: `RuleLemmas.lean` is installed as
`Proofs/RuleLemmas.lean` and `Rules/<Rule>.lean` as `Proofs/Rules/<Rule>.lean`,
which is what the `import <Calc>.Proofs.Rules.<Rule>` lines that the former
carries name. Every other file is installed at the root of the package, where
its name already is its import.

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
still generating the remaining Lean modules and per-rule files. This also
removes a stale `Parser.lean` from the selected final output directory.

Pass `--lean-config FILE` to name the termination clauses of the input's own
programs where the input was given already written out rather than as a
configuration set; see "Why the generated Lean terminates" above.

The generated modules carry only the `native_` definitions the input reaches,
so the same signature compiled for fewer rules publishes a smaller native
layer; see "Trimming the native layer" above.

Generated files are written to `tools/eoc/out/lean/` by default, including
per-rule files in `tools/eoc/out/lean/Rules/`. `Parser.lean` is the minimal
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
`lean` pipeline through `driver.py`, then copy the generated Lean files from
`tools/eoc/out/lean`, including `Rules/*.lean`, into a downstream Logos tree.
The destinations are the ones named in [`cpc/README.md`](cpc/README.md), each
overridable with an environment variable.

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

Pass `--no-trim-natives` to the last of those to emit the whole of the native
layer rather than the part of it the input reaches, which is for reading what
was dropped; see "Trimming the native layer" above.

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
