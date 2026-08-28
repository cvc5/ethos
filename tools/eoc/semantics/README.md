# The signature configuration

The files here say what a symbol means to the model, once, in the vocabulary of
SMT-LIB and of the input. `tools/eoc/sem_compile.py` compiles them into the
signatures written in the deep embedding that the model-smt stage reads and the
Lean clauses the lean-meta stage reads, all of which are generated in full.

This is the reference for the language they are written in: the grammar, every
entry with its attributes, the four levels and how a body is cast, what the
compiler checks, worked examples, and what every diagnostic means.

**The compiler knows the naming conventions of the embedding and nothing else:**
how to read an s-expression, how a name is spelt at each of four levels, and how
to read the vocabulary of the embedding out of the files that define it -- that
a bare name is `$sm_X` where a term is wanted, `$tsm_X` where a type is and
`$smtx_model_eval_X` where a value is, that `"X"` is `$native_X` and `SmtX` is
`$smt_X`. Which programs a symbol compiles to, what each declares and what an
argument stands for in one are said by the configuration, in the forms below.

---

## Contents

1. [The shape of a run](#1-the-shape-of-a-run)
2. [Lexical structure](#2-lexical-structure)
3. [Grammar](#3-grammar)
4. [Files and blocks](#4-files-and-blocks)
5. [The shape of what is written](#5-the-shape-of-what-is-written)
6. [Entries](#6-entries)
7. [The four levels](#7-the-four-levels)
8. [Casting](#8-casting)
9. [Checks](#9-checks)
10. [Worked examples](#10-worked-examples)
11. [Recipes](#11-recipes)
12. [Diagnostics](#12-diagnostics)

---

## 1. The shape of a run

A **set** is one file, and compiles to two: the signature written in the deep
embedding that the model-smt stage reads, and what the set says the generated
Lean is to be told, which the lean-meta stage reads. There are two sets:

```text
smt.eos              ->  tools/eoc/out/smt_defs.eo
                         tools/eoc/out/smt_termination.lean
development-cpc.eos  ->  tools/eoc/out/user_defs.eo
                         tools/eoc/out/user_termination.lean
```

Neither set is read while the other is compiled, so a form belongs to one
signature by the directory it stands in and by nothing else.

**`smt.eos` is the target**: what an SMT-LIB symbol means to a model, the type
of a term and the value of one. Every input is compiled through it, so what it
says is what a model of any input means, and nothing about an input is asked of
it. A run names another with `--semantics`.

**`development-cpc.eos` is a test**, kept so that the compiler and every stage
after it have a real signature to run over; CI compiles it on every push. **The
official semantics of CPC lives in the Logos repository**, which is what a run
that means to say something about CPC names with `--signature`. Nothing keeps
the copy here in step with it, and a set named that way compiles beside itself,
so running against the official one leaves this tree alone.

Compiling one set is four steps:

1. Read the file into **blocks**, expanding macros as they are met. Its
   heading is what the generated file says about itself.
2. Take the shape of what it writes from the tool, by whether it is the target
   or an input.
3. Render each block: a symbol becomes a constructor and one program per
   aggregate it contributes to; a program becomes itself with the terms of its
   cases cast; anything else is refused. What reaches the
   other file rather than this one -- the Lean a method says -- is gathered as
   it goes, and a block left with nothing is no block at all.
4. Check that every helper a block came to name is written out by some file of
   the same set, and that no block uses a name a later block defines.

```bash
python3 tools/eoc/sem_compile.py                    # write what each set compiles to
python3 tools/eoc/sem_compile.py --check            # say whether the generated files are current
python3 tools/eoc/sem_compile.py --out-dir D        # write elsewhere
python3 tools/eoc/sem_compile.py CONFIG...          # one shipped set rather than both
python3 tools/eoc/sem_compile.py --signature CONFIG # a set of another tree, as an input
python3 tools/eoc/sem_compile.py --semantics CONFIG # ... as an SMT-LIB semantics
```

The eoc driver runs the compiler before the model-smt stage, so the generated
files are current whenever that stage reads them; `--signature` names the
central file rather than what it compiles to. A file is written only where its
text changed.

The modules are `sem_lang.py` (the reader, blocks, levels, casting, and the
entries), `sem_target.py` (the shape of what each kind of entity writes) and
`sem_compile.py` (the driver, what each set compiles to, and `--check`).

---

## 2. Lexical structure

A file is a sequence of s-expressions.

| token | written | note |
| --- | --- | --- |
| list | `(a b c)` | the whitespace between items is kept, so a form comes out laid out as it was written |
| symbol | `bvadd`, `$sm_x`, `@purify`, `<=` | anything up to whitespace, a bracket, a quote, a bar or `;` |
| keyword | `:eval` | a symbol beginning with `:` |
| integer | `42` | decimal digits only; `-1` is a symbol, not an integer |
| native | `"z_+"` | a double-quoted name; see [The four levels](#7-the-four-levels) |
| comment | `; ...` | to end of line |

Comment lines written **directly above** a form, with no blank line between,
are that form's documentation. A blank line ends a comment block, which is what
lets a file carry a heading of its own without it becoming the first form's
documentation.

Where a comment block reaches a generated file depends on what it is above:

- above a `(program ...)`, it is what that block says for itself and is
  emitted, a program being emitted as itself;
- above a `define-symbol`, it documents the *configuration* and is not emitted,
  the symbol compiling to something other than itself;
- above a `; -- X` line, it documents the configuration and is not emitted;
- below a `; -- X` line, it belongs to the form beneath it and follows the two
  rules above.

---

## 3. Grammar

Everything is an s-expression, so the grammar is mostly one line per form.
`UPPERCASE` is a token, lowercase a rule, `[x]` optional and `x*` zero or more;
anything else stands for itself.

### Tokens

```text
NAME        bvadd   $sm_x   @purify   <=   smt.binary   ->
            any run of characters up to whitespace, a bracket, a quote,
            a bar or a semicolon
KEYWORD     :eval                       a NAME beginning with a colon
INTEGER     42                          decimal digits, and nothing else
NATIVE      "z_+"                       a NAME in double quotes
STRING      "core.eo"                   likewise
```

### Terms

What every body, pattern and type is built from.

```text
term     ::=  NAME  |  INTEGER  |  NATIVE
           |  (NAME term*)
           |  (NATIVE term*)
           |  (eo::define ((NAME term)) term)

pattern  ::=  term          read as a matcher; a NAME it holds it binds,
                            and a $NAME of the embedding matches itself
type     ::=  NAME  |  NATIVE  |  (type*)
```

### Forms

A file is a sequence of these.

```text
(section STRING)                                    opens one theory

(define-macro NAME (NAME*) term)                    see Entries
(program NAME (declaration*) :signature (type*) type (case*))
(define-symbol NAME (parameter*) attribute*)
(define-sort NAME (parameter*) attribute*)          the target only
(define-value NAME (parameter*) attribute*)         the target only
(define-literal NAME (parameter*) attribute*)       the target only
(define-method NAME attribute*)                     an input only
(define-rule NAME attribute*)                       an input only

anything else                                       refused
```

The attributes of a symbol or of a type are:

```text
parameter    ::=  NAME  |  (! NAME :raw)  |  (! NAME :type)

attribute    ::=  :AGGREGATE [pattern] term     a case of that aggregate
               |  :HELPER (pattern*) term       a case of its helper, one
                                                pattern per argument
               |  :overload NAME
               |  :exclude
               |  :keep
               |  :lean STRING

declaration  ::=  (NAME type)
case         ::=  (pattern term)
```

`:AGGREGATE` and `:HELPER` stand for the names the set declared -- `:typeof`,
`:value` and `:eval` in semantics/smt.eos, `:term`, `:type` and `:is-list-nil`
in semantics/development-cpc.eos.

An attribute that gives a case may be written more than once, each occurrence
adding one. Whether it was given a pattern is read off what follows: a value is
never a keyword, so a second value is what the case returns and the first is
what it matches.

`:AGGREGATE` and `:HELPER` are the attribute names the *shape* of the set
gives them, which is not something a signature says; see
[The shape of what is written](#5-the-shape-of-what-is-written).

---

## 4. Files and blocks

### The file a set stands in

Its **heading** -- the comment lines at the top, up to the first blank line --
is what the generated file says about itself. After that it holds its theories,
each opened by a section:

```lisp
;-----------------------------------------------------------------------------
(section "Bit-vectors")
;-----------------------------------------------------------------------------
```

A section says where one theory ends and the next begins. It reaches no
generated file; what it does is **close whatever block is open**, so that a
program at the head of a theory opens a block of its own rather than joining
the theory before it. The two sets hold theirs in the order their blocks are
emitted:

```text
smt.eos                             development-cpc.eos
the vocabulary of the embedding     the vocabularies of the two layers
the types                           the core symbols -- ite, =, distinct
the values                          arithmetic
the literals                        arrays
the core symbols                    bit-vectors
arithmetic                          strings, sequences, regular expressions
arrays                              sets
bit-vectors                         datatypes and tuples
strings, sequences                  quantifiers, skolems, the binder left out
sets                                the type constructors
the methods of the embedding        the methods of the signature
```

The SMT-LIB semantics has no section of datatypes, quantifiers or type
constructors of the input, since it has nothing to say about them: what the
input writes with those is eliminated on the way in. Each set keeps an order of
its own, which is what one source order could not give: `smt_defs.eo` has
`div_total` before `div` and `user_defs.eo` the reverse.

**What a set compiles to it does not say.** The model-smt stage reads two
files: the SMT-LIB semantics, which is the target of the compilation, and one
signature of the input whichever input a run compiles. Which of the two a set
is is said by the role a run gives it -- the two the tool ships with have
theirs fixed, and any other is given one by the option that names it,
`--semantics` for a target and `--signature` for an input, never by what its
file is called -- and where what it compiles to is written is the tool's to
say, in `SMT_TARGET` and `INPUT_TARGET` in `tools/eoc/sem_compile.py`.

Those are where the sets the tool ships with compile to, `tools/eoc/out`, which
nothing checks in: what is kept is the configuration. **Any other set compiles
beside itself**:
where it stands is the only place the tool knows of, so a set that lives in
another tree writes what it compiles to into that tree. That is what lets a
run name one: `--signature` for the signature of the input and `--semantics`
for the SMT-LIB semantics it is written against, either of which may be a set
or a signature already written out.

A set is recognised by holding a `define-symbol`, which a signature written out
never does; that is also how the two options tell one from the other.

### Blocks

The generated file is a sequence of **blocks**, each opened by a `; -- X` line.
A block is what the model-smt stage takes or drops as a unit, so a symbol keeps
the programs its cases name in its own block.

- A `; -- X` comment line opens a block named `X` and gathers the forms after
  it into that block.
- Without one, each entry opens a block of its own, named after what it
  defines: a symbol after itself, a program after the symbol its name ends
  with when its name begins with an aggregate's case prefix, and after itself
  otherwise.
- An entry written under a `; -- X` line whose name it carries joins that
  block; so does a program, which belongs to no symbol.

Naming the same block twice is an error.

---

## 5. The shape of what is written

**A signature does not say this, and there is no form of the language for it.**

What the generated files look like -- which programs there are, what each
declares and matches, and which aggregate its cases are spliced into -- is
settled by the stage that reads them: `DefsFile::read` in
`plugins/model_smt/defs_reader.cpp` takes a definitions file apart by the name
of each program. That is a contract between the compiler and that stage, so it
lives in the compiler, in `tools/eoc/sem_target.py`, and a signature says only
what its symbols mean.

A set holds one **kind** of entity or several, each with a shape of its own:
the SMT-LIB signature declares its symbols and the types they are of, and the
two are read apart by the form that declares one.

| kind | declared by | writes, per entity |
| --- | --- | --- |
| a symbol of the **target**, `semantics/smt.eos` | `define-symbol` | a constant of the embedding and the macro that applies it; a case of `$smtx_typeof` under `:typeof`; a case of `$smtx_model_eval` under `:value`, or the program it hands its work to under `:eval` |
| a type of the **target**, `semantics/smt.eos` | `define-sort` | a constant of the embedding and the macro that applies it; a case of `$smtx_type_wf_rec` under `:wf`, of `$smtx_type_bounded` under `:bounded`, of `$smtx_type_default` under `:default` |
| a value of the **target**, `semantics/smt.eos` | `define-value` | a constant of the embedding and the macro that applies it; a case of `$smtx_typeof_value` under `:typeof`, of `$smtx_value_canonical_bool` under `:canonical` |
| a literal of the **target**, `semantics/smt.eos` | `define-literal` | a constant of the embedding and the macro that applies it; the two cases a symbol writes, `:typeof` and `:value`, over what it carries rather than over terms |
| a symbol of an **input**, `semantics/development-cpc.eos` | `define-symbol` | a case of `$eo_to_smt` under `:term`; a case of `$eo_to_smt_type` under `:type`; the predicate the desugar stage asks under `:is-list-nil` |
| a method, either set | `define-method` | nothing of the model: what is said about a program is said to a stage -- the Lean clause of `:lean`, which is written into the Lean file of the set, and `:exclude` |
| a rule of an **input**, `semantics/development-cpc.eos` | `define-rule` | the same, for a proof rule, which says only that it is left out |

So the attribute names an entity may carry -- `:typeof`, `:value`, `:eval`,
`:wf`, `:bounded`, `:default`, `:term`, `:type`, `:is-list-nil` -- come from
there, and so does what an
argument stands for in each, which the sections below refer to as the
aggregate's `:stands-for`.

`sem_target.py` gives each as the text it produces, with holes -- `{symbol}`
for the name of the symbol and `{i}` for the number of an argument -- so it is
read rather than parsed. It is not a file anyone editing a signature needs to
open.

## 6. Entries

### `(define-symbol NAME (param...) attr...)`

One symbol, and one case per aggregate it contributes to. **It says nothing
about types.** An attribute is named after the aggregate it gives a case of,
and the aggregates are read apart, so a symbol whose value matches any sequence
while its type demands a string simply says the two separately.

No attribute means two things. An aggregate is named for what a symbol
contributes to it, so `:typeof` is the type *of* a term symbol and `:term` and
`:type` are what a symbol of the input becomes, one per level the input has;
`:type` then says the same thing wherever it stands, in an attribute and in the
parameter marker `(! v :type)` alike -- **a type**.

#### Parameters

| written | kind | meaning |
| --- | --- | --- |
| `v` | `plain` | an ordinary argument |
| `(! v :raw)` | `raw` | one that reaches a case as the term was written |
| `(! v :type)` | `type` | a type rather than a term |
| `(v T)` | `plain`, of `T` | one of the type named, written the way a program's parameter list writes one |

The two marked kinds are annotated the way SMT-LIB annotates a term. The last
is for a kind of entity whose arguments are not all of one type -- a value of
the embedding is built over a native of one sort or another -- and it settles
what a case calls each argument: the program the cases are spliced into
declares each name once, so an argument is named after the type it is of
rather than `x1` twice. The name is a letter for that type and the place the
argument stands at -- `s1` for a native string first, `T2` for a type second,
`x3` for a term third -- and `SLOT_BY_TYPE` in `tools/eoc/sem_target.py` is
where a type is given its letter. Two types may not share one, and a type with
none is an error rather than a guess.

What each stands for in a body is the aggregate's business. In
`semantics/smt.eos` a `:raw` argument -- an index -- stands for the term itself
where the type rule reads it and for its value where the evaluator does, and
the entry says nothing about that. Naming a parameter twice is an error.

#### Attributes

The attributes a symbol may carry are exactly the aggregate names of its set,
their helper attributes. For the two sets in the tree:

| set | attributes |
| --- | --- |
| `semantics/smt.eos`, a `define-symbol` | `:typeof`, `:value`, `:eval`, `:overload`, `:exclude`, `:keep` |
| `semantics/smt.eos`, a `define-sort` | `:wf`, `:bounded`, `:default`, `:overload`, `:exclude`, `:keep` |
| `semantics/development-cpc.eos`, a `define-symbol` | `:term`, `:type`, `:is-list-nil`, `:overload`, `:exclude`, `:keep` |
| `semantics/smt.eos`, a `define-value` | `:typeof`, `:canonical`, `:overload`, `:exclude`, `:keep` |
| `semantics/smt.eos`, a `define-literal` | `:typeof`, `:value`, `:overload`, `:exclude`, `:keep` |
| a `define-method`, either set | `:lean`, `:exclude` |
| a `define-rule`, `semantics/development-cpc.eos` | `:exclude` |

Every attribute that gives a case has the macros of its file expanded out of it
before anything else sees it, and every one may be **given more than once**,
each occurrence adding a case.

#### Cases

An attribute takes one value or two. Two means the first is **what the case
matches** and the second is what it returns; one means the case matches what
the aggregate's `:matches` says. A value is never a keyword, so what follows
tells the two apart without marking either.

```lisp
(define-symbol forall ((vs :raw) body)
  :term (forall $eo_List_nil body)  none
  :term (forall vs body)            (not ($eo_to_smt_exists vs (not body))))
```

A case binds **only what its own pattern matches**, and the program declares
one parameter per name it bound, in the order the pattern bound them. So the
two cases above bind a different thing in the same place, and a return that
names something its pattern did not bind is an error rather than a program that
will not load. The program declares as many parameters as the widest case
needs.

Beside the arguments, a body may name what `:context` and `:own` declare -- the
model of an evaluation, the type a transformation is of -- and each stands for
itself.

#### A case of the helper

A case of an aggregate's `:helper` -- `:eval` in `semantics/smt.eos` -- is an
ordinary case: what it matches is **one pattern per argument**, and what it
gives is a term.

```lisp
:eval ((smt.seq s) (smt.numeral i) (smt.numeral n))
      (of_chars s ("seq.extract" (chars s) i n))

:eval ((smt.binary n x) (smt.binary m y))  (of_width n ("z_+" x y))
:eval ((smt.map m1) (smt.map m2))          ("eval_map_diff_msm" m1 m2)
```

**What a pattern binds, the program declares**, and what each name is declared
as is read off the declaration of what it is applied to: `smt.binary` is
`$vsm_binary`, which the embedding declares as `((w $native_Int) (v
$native_Int))`, so `(smt.binary n x)` gives `n` and `x` those types. A pattern
that is a bare name matches any value and is of the type the aggregate says
each argument is; a `$`-name is not a name of the case but a constructor that
carries nothing, so `$vsm_true` matches itself alone and declares nothing.
Nothing states a type twice, here or anywhere else.

Putting a value back together is a **macro of the theory** -- `of_width` for a
bit-vector reduced to a width, `of_chars` and `of_text` for a sequence and a
string packed back up -- so a case that builds one says what it is building.

Two cases may take a name apart the same way and then declare it once: the
parameters of a program are of the program, not of a case of it. Declaring one
name as two different things is an error.

A case whose patterns are all names it *binds* leaves nothing over, so the
case for what is left could never be reached and is not written; otherwise the
aggregate's `:otherwise` writes it. A constructor that carries nothing is a
name too, so `(smt.true x y)` leaves the rest over like any other pattern.

#### Saying a symbol contributes nothing

An attribute given the bare name `none`, and nothing else, says the symbol
contributes nothing to that aggregate: no case is spliced and no program is
written for it. That is not the same as saying nothing at all, which takes the
aggregate's `:default`.

```lisp
(define-symbol @@TypedList.cons (x xs)
  :term none
  :is-list-nil (@@TypedList.nil T) true)
```

The list the desugar stage gathers an n-ary application into is a symbol of the
input that never reaches the model, so it becomes nothing; it still carries the
predicate that stage asks for the unit an application may drop.

#### Leaving something out altogether

`:exclude` says the compilation has no place for what says it: SMT-LIB gives a
proof-level binder no meaning, so rather than a model, `lambda` says it is left
out. What dropping a symbol would otherwise leave behind is written out and
says the same for itself, since no dependency closure is computed -- a program
of the signature with `define-method`, a proof rule with `define-rule`.

```lisp
(define-symbol lambda ()
  :exclude)

(define-method $get_lambda_type :exclude)

(define-method $beta_reduce :exclude)

(define-rule beta-reduce :exclude)
```

An excluded entity contributes to nothing, so no case and no program is written
for it. What is written instead is `(echo "eoc-exclude KIND NAME")`, the kind
being what the form that declared it says one is -- symbol, method or rule --
which `Desugar::echo` reads and `Pipeline.defs_excludes` in
`tools/eoc/driver.py` collects from the generated file; a rule among them is
also left out of `--all-rules`.

#### Keeping a symbol the input trims away

A block is kept when the input declares its symbol or when something kept
names it, so a calculus trimmed to a handful of rules leaves out the symbols
those rules never mention. `:keep` says a symbol is not to be left out:

```lisp
(define-symbol ite (c x y)
  :keep
  :typeof ($smtx_typeof_ite c x y)
  :eval (smt.true x y)  x
  :eval (smt.false x y) y)
```

It is for a symbol the *embedding* names rather than the input: `ite` and `=`
are what the hand-written proofs about the generated Lean are written over,
whatever a calculus trims away. What is written is `(echo "eoc-keep symbol X")`,
which `DefsFile::select` in `plugins/model_smt/defs_reader.cpp` honours, keeping
the block the way one of a declared symbol is.

#### `:overload NAME`

What the symbol is written under, where that is not its own name. A signature
may not declare one name twice, so the desugar stage gives an *overload* of a
symbol a name of its own; the entry is written under the name the input knows
and says what that name is.

```lisp
(define-symbol - (x)
  :overload $eoo_-.2
  :term (uneg x))
```

The name it gives is what the symbol is called everywhere else: the block it
opens, the case it matches, and the program that case is written as.

#### Defaults

A symbol that says nothing about an aggregate takes that aggregate's
`:default`, if it has one and either the aggregate is `:primary` and the symbol
says nothing about any `:sole` aggregate, or the symbol wrote cases for that
aggregate's helper.

So in `semantics/development-cpc.eos` a symbol that says nothing at all
transforms pointwise, a symbol that says only `:is-list-nil` still transforms
pointwise, and one that says `:type` -- a type constructor -- does not, `type`
there being `:sole`. In `semantics/smt.eos`, a symbol with `:eval` and no
`:value` gets a `value` case that calls its helper.

A symbol that would emit nothing at all is an error.

### `(define-sort NAME (param...) attr...)` -- the target

One type of the signature: the constructor of the embedding for it, the macro
that applies it, and what the three programs written over the types say about
it. A body writes the bare name of a type -- `Bool`, `(Seq T)`, `(BitVec n)` --
so this is what says there is one.

```lisp
(define-sort Set (T)
  :wf ($smtx_type_wf_component_rec T)
  :bounded ("and" ("not" u) ($smtx_type_bounded u T))
  :default ($smtx_empty_set T))
```

A parameter is written the way a symbol's is, and means one thing less: a plain
one is a type, and `(! v :raw)` the index a type is built over rather than a
type, as the width of a bit-vector is. **A parameter stands for itself**, since
a type is already of the embedding and there is nothing to ask of it first.

| attribute | says | written at |
| --- | --- | --- |
| `:wf` | whether the values of the type are a set at all | native level |
| `:bounded` | whether it has one value, where `u` is true, or finitely many, where `u` is false | native level |
| `:default` | the value a model reaches for where it has to name one of the type | value level |

`u` is what `:bounded` is given beside the type, the way `M` is what a `:value`
is given beside the term, and stands for itself. A type that says nothing about
an attribute is answered for by the program the cases are spliced into: it is
well-founded, it is not bounded, and it has no default.

A type is the **embedding's own**, so every block one opens is kept whether or
not the input declares the name, as if it had said `:keep`: a calculus trimmed
to a handful of rules has the whole of `SmtType` all the same. The order the
types stand in here is the order their constructors are given, and `typeKey` in
the generated `SmtValueOrder` -- so which values count as canonical -- follows
it, so a type is added at the end rather than in the middle.

The types the embedding keeps for itself -- `none`, `Datatype`, `TypeRef`,
`USort`, `FunType`, `DtcAppType` -- are not here: they are how the embedding
represents what a calculus declares rather than types of a theory, and stand in
`plugins/model_smt/model_smt.eo` with the rest of the same three programs.

So is a type that is one of the sorts under a second name -- `Array`, which is
a `Map`, and `String`, which is a `(Seq Char)`. Those stand there rather than
here because a bare name at type level is `$tsm_X` whichever signature writes
it, so an input that names an array is written against the embedding's `Array`;
a macro would carry only across the files of the set that declared it.

### `(define-value NAME (param...) attr...)` -- the target

One value of the signature, i.e. what a term of it evaluates to in a model. It
writes the constructor of the embedding for the value and the macro that
applies it, the way a type does, and one case of each of the two programs
written over the values.

```lisp
(define-value Set ((m SmtMap))
  :typeof ($smtx_map_to_set_type (smt.typeof_map_value m))
  :canonical ("and" ($smtx_map_canonical m)
               ("veq" ($smtx_msm_get_default m) smt.false)))
```

Each parameter says the type it is of, since a value is built over natives of
several sorts, over types, and over the shapes a map and a sequence are; what
it stands for in a body is itself.

| attribute | says | written at |
| --- | --- | --- |
| `:typeof` | the type a term whose value it is would be of | type level |
| `:canonical` | whether it is the one spelling of what it denotes | native level |

A value that says nothing about an attribute is answered for by the program its
cases are spliced into: it is of no type, and it is canonical.

An entity is named after the constructor it declares -- `Boolean`, not `bool` --
so `$emb_vsm.Boolean` and `$vsm_Boolean` are what it writes. **A value has no
bare name**: what a body writes is `smt.bool`, a macro of the set, and the
vocabulary block is the one place the macro of a value is named. The block a
value opens is named after its constructor for the same reason a type's is not:
`Seq` is a type and a value both, and a block is named once.

Like the types, the values are the embedding's own, so every block one opens is
kept whatever a calculus declares, and they stand in the order their
constructors are given -- `valueKey` in the generated `SmtValueOrder` follows
it -- so a value is added at the end.

### `(define-literal NAME (param...) attr...)` -- the target

One literal of the signature, i.e. a term the embedding builds over a native
rather than over terms of its own. It writes the constructor and the macro the
way a value does, and the two cases a symbol writes.

```lisp
(define-literal Binary ((w "Int") (v "Int"))
  :typeof ("ite" ("and" ("z_<=" 0 w) ("z_=" v ("mod_total" v ("z_pow2" w))))
            (BitVec ("z_to_n" w))
            none)
  :value (smt.binary w v))
```

| attribute | says | written at |
| --- | --- | --- |
| `:typeof` | the type a term of it is of | type level |
| `:value` | what it evaluates to in a model | value level |

Each parameter says the type it is of, and what it stands for in a body is
itself: it is a native the term carries rather than a term whose type or value
is asked for. That is the whole of the difference from a `define-symbol`, whose
arguments are terms and stand for what is asked of them.

The cases go where a symbol's go, into `$smtx_typeof` and `$smtx_model_eval`,
and stand before them. So do the constructors: a literal is the embedding's own
and its block is kept whatever a calculus declares, and the order of the
constructors of the embedding is the order the configuration gives, which the
generated `SmtTerm` follows. A literal is therefore added at the end.

The block a literal opens is named after the constructor it declares, since
`String` is a type and a literal both. That is also what tells the stage
reading the file that the constructor is one of the embedding's own rather than
one of a symbol written over them, see `DefsBlock::d_literal` in
`plugins/model_smt/defs_reader.h`.

### `(define-method NAME attr...)`, `(define-rule NAME attr...)`

One program written out in Eunoia -- of the embedding, in the target, and of
the signature itself in an input -- and one proof rule. Neither names what it
takes: what is said is said about the whole of it.

```lisp
(define-method $smtx_model_eval
  :lean "termination_by structural t => t")

(define-method $beta_reduce :exclude)

(define-rule beta-reduce :exclude)
```

**`:lean`** is the Lean text that follows the definition the lean-meta stage
writes for the program: why its recursion terminates, and anything that has to
be proved once about the definition. It is appended as it stands, so it is
written as a string, over as many lines as it takes:

```lisp
(define-method $smtx_field_type_default
  :lean "termination_by T ddF => 2 * (sizeOf T + sizeOf ddF) + 3
decreasing_by
  all_goals simp_wf
  all_goals omega")
```

The clauses of a set are written to the Lean file of that set, in the order the
set gives them, and the comment above a method is prose of that file, since a
clause holds no comment of its own. Methods that stand together and say the same
clause come out under one heading.

**`:exclude`** says the compilation has no place for it. What is left out is not
always a symbol: dropping the binder of CPC drops the methods that reduce an
application of one and the rule written over them, and each says so where it
stands.

### `(program NAME (param...) :signature (T...) R (case...))`

One program of the embedding, written **exactly as a definitions file writes
one**. What it compiles to is that same form with the *terms of its cases*
cast; everything else -- the parameters, the signature, the whitespace, a
comment between two cases -- comes out as it was written.

Its parameters stand for themselves, being of the embedding already, which is
what makes a case read like the term it is.

Three vocabularies meet in a parameter list and in a signature, each named as
it is named everywhere else:

| written | is |
| --- | --- |
| `"Int"` | a native type |
| `SmtTerm` | a type of the embedding, without the `$smt_` it is declared under |
| `Type`, `$eo_List`, `(@@TypedList T)` | a type of the *input*, as the input writes it |

Naming a type the embedding has no such type for is caught here rather than by
ethos.

**The signature is what says how a case is read**, place by place. A place
whose declared type is one of the input is taken as the input wrote it, and
what such a place *matches* is of the input too, and is transformed wherever
the case then puts it where the embedding is wanted. Every other place is cast
in the vocabulary its type names.

```lisp
(($eo_to_smt_distinct_pairs s (@@TypedList.cons x xs))
   (and (not (= s x)) ($eo_to_smt_distinct_pairs s xs)))
```

`s` was matched at a `SmtTerm` and is one already; `x` and `xs` were matched
inside a list declared `(@@TypedList T)`, so `x` under `=` is `($eo_to_smt x)`
while `xs` at the program's own second place is `xs`.

A symbol names a program written above it simply by being of the same name: the
program an aggregate's `:default` reaches for is what a symbol's helper cases
compile to, so a symbol may write that program out by hand and say no helper
cases at all.

### `(define-macro NAME (param...) body)`

An idiom the bodies of that file would otherwise repeat. It is expanded before
anything else sees it -- in an attribute and in the cases of a program alike --
and reaches no generated file. A macro may be written with the ones above it,
and macros carry across the files of a set in the order they are included.

Each set also has an `embedding.eo` of nothing but macros: the vocabulary of
the embedding a body would otherwise write out, named under the prefix `smt.`.
See "What a `$`-name is" below.

This is where an idiom that would otherwise be builtin lives: `of2`, the type
of a symbol both of whose arguments are of a type given; `chars` and `text`,
what the operators of a sequence and of a string are given; `msb`, the sign bit
of a bit-vector value; `width`, which differs by set because one has the value
of a bit-vector in hand and the other the term.

Only `eo::define` is builtin, and only because what it binds is of the level
the body reads it at.

### Nothing else

Every form of a set is one of the entries above, a `program`, a `define-macro`
or a `section`. **Anything else is refused**, and that includes a bare
`declare-const`, `declare-parameterized-const` or `define`.

Nothing is carried over as the text it is. A form emitted untouched would put
into the generated file something the compiler never read, so what it names
could not be checked against the vocabulary, ordered against the other blocks,
or trimmed with them; and a name it defined would be one more thing that has to
be kept in step by hand.

So a set says what a theory **does**, and never what the embedding **is**. A
declaration of the embedding -- the `$smt_Map` a map value is built over, the
`$emb_msm.` constructors that build one, the `$vsm_` name of a value it spells
out -- is written in `plugins/model_smt/model_smt.eo`, which is the one place
that says what the embedding is built from. A set then writes the programs over
it: `$smtx_msm_lookup`, `$smtx_typeof_map_value`, `$smtx_map_canonical`, each a
`program` beside the sort it belongs to.

If what you are reaching for is an idiom rather than a definition, write a
`define-macro`: it is expanded before anything else sees it and reaches no
generated file, which is what an inlined `define` amounted to anyway.

---

## 7. The four levels

A term of the embedding is written in one of four vocabularies, and **which one
is said by the type of the place it stands in**. That is the whole of the
difference, and it falls on a bare name and a whole number alone:

| level | said by | `f`, a bare name | `0`, a whole number |
| --- | --- | --- | --- |
| native | a `"..."` type, e.g. `"Int"` | must be bound | `$native_z_zero` |
| value | `SmtValue` | `$smtx_model_eval_f` | `$vsm_z_zero` |
| term | `SmtTerm` | `$sm_f` | `$sm_z_zero` |
| type | `SmtType` | `$tsm_f` | -- |

Two further levels appear in a signature but have no names of their own:
`embedding`, for a type of the embedding a bare name is never of, as `$smt_Map`
is; and `input`, for a type of the input, whose terms are taken as the input
wrote them.

The level of an **argument** is read off the declaration of what it stands
under, so `($vsm_numeral 0)` puts a native where `(bvudiv x 0)` puts a value; a
place the declaration leaves open, as a branch of `ite` is, is of the level
around it. The vocabulary is read from `plugins/desugar/native_embed.eo`,
`plugins/desugar/eo_desugar.eo` and `plugins/model_smt/model_smt.eo`, together
together with the programs the set itself writes out, so a native that does not
exist or is given the wrong number of arguments is caught by the compiler
rather than by ethos.

A native in quotes and a `$`-name of the embedding are what they are wherever
they stand, so the level never has to be said twice.

---

## 8. Casting

A body is written in the *surface* -- the vocabulary of SMT-LIB and of the
input -- and cast into the deep embedding.

| written | becomes |
| --- | --- |
| `(f a b)`, `f` | the name of that level's family, e.g. `($sm_f <a> <b>)` where a term is wanted and `($smtx_model_eval_f <a> <b>)` where a value is |
| `x`, an argument | what the aggregate's `:stands-for` says for the kind it was written as |
| a name a case or a shape bound | itself |
| `$g`, `($g a)` | itself. This is how a program of the file is called, and how a macro of the embedding such as `$dd_cons` or `$sm_none` is named |
| a name of the *input* | itself where the input is wanted; the aggregate of the level applied to it where the embedding is |
| `3` | the whole number, as that level writes one |
| `"ite"`, `("z_<=" a b)` | `$native_ite`, `($native_z_<= <a> <b>)` -- a native, named without the `$native_` it is defined under |
| `(eo::define ((v e)) body)` | the same, with `v` standing for itself in `body`, and `e` written at the level the body reads `v` at |

An `eo::define` whose body reads the name back **at most once**, or whose value
is already atomic, is written where it stands rather than bound: it would only
be a name for a name. The term is the same either way.

A term is laid out as it was written: a case that runs to several lines comes
out over several lines, so rewriting the names of a program does not reflow it.

### What is refused

Six families of name are refused rather than passed through, each answered
with the name to use instead:

| written | answer |
| --- | --- |
| `$emb_X` | write the macro that applies it |
| `$sm_X` | write `X`, the symbol of the signature |
| `$native_X` | write `"X"` |
| `$smt_X` | write `SmtX` |
| `$tsm_X` | write `X`, the type constructor |
| a name the compiler writes, e.g. `$smtx_model_eval_X`, `$eoc_eval_X` | write `X`, the symbol it was written for; naming the symbol is the whole of how a body reaches it |
| `$eo_to_smt`, `$eo_to_smt_type`, `$smtx_model_eval` | the aggregate this case is a part of; the place a name stands in already says it |

Naming the *operator* a native is defined as -- `"zleq"` for `$native_z_<=` --
is likewise refused with the name to use.

### What a `$`-name is

**In a body, a `$`-name is a program of the same set and nothing else.**

A term of the deep embedding belongs to one of two layers -- the SMT-LIB
signature a model is of, and the input as the desugar stage embeds it -- and a
bare name is one of the family the *level* it stands at is of, so neither
layer's constructors have a bare name of their own. Each set names the ones it
uses in an `embedding.eo` of nothing but macros, under one prefix per layer:

| prefix | the layer | example |
| --- | --- | --- |
| `smt.` | the SMT-LIB signature and its methods | `smt.binary`, `smt.map_lookup`, `smt.typeof` |
| `eo.` | the input, as the desugar stage embeds it | `eo.list_cons`, `eo.var`, `eo.numeral` |

```lisp
(define-macro smt.binary (w v)      ($vsm_binary w v))
(define-macro smt.map_lookup (m i)  ($smtx_msm_lookup m i))
(define-macro smt.bit_true ()       $vsm_binary_bit_true)
(define-macro eo.list_cons (x xs)   ($eo_List_cons x xs))
```

So a transformation reads `eo.` and writes `smt.`, and says which layer it is
speaking of at every step. semantics/smt.eos names only the first, having no
input to read; semantics/development-cpc.eos names both.

A macro of no arguments stands for its body wherever its name stands, so
`smt.bit_true` and `eo.list_nil` are written bare. A macro is matched by its
whole name before a name is read as a symbol, which is why a prefix here cannot
be a *family* prefix in the caster: `seq.` would swallow `seq.empty`, a symbol
of the signature. A macro named after a symbol of its own set is refused for
the same reason.

Because a macro is expanded before anything else sees it, and the text a form
is written as is recomputed as it expands, a macro may stand in a **pattern**
as well as in a term -- which is what lets `(eo.list_cons (eo.var s T) vs)`
match what the desugar stage built.

So the kinds of `$`-name that remain are these, and every one in the tree today
is one of them:

| kind | example | why a `$` |
| --- | --- | --- |
| a program the configuration writes | `$smtx_typeof_bv_op_2`, `$eo_to_smt_exists` | it is a program of this set, named as itself -- never under a name the compiler writes, see [Casting](#8-casting) |
| either layer, in `embedding.eo` | `$vsm_binary`, `$smtx_msm_lookup`, `$eot_Var` | that file is where the two layers are named; everywhere else writes `smt.` or `eo.` |
| either layer, in a **declaration** | `$vsm_seq` in a shape's `:match`, `$smtx_typeof` in an aggregate's `:program` | naming the embedding is what a declaration is for |
| the name of an **overload** | `$eoo_-.2` in an entry's `:overload` | it is the name the desugar stage gives that symbol, so the entry says it as it is |
| a **type** of the input, in a signature | `$eo_Term`, `$eo_List` | a signature is not a term, so no macro reaches it; a type of the input is named as the input names it |
| a template of a declaration | `$emb_sm.<symbol>`, `$eoc_eval_<symbol>` | it names what is written or spliced |

A **type** constructor is not among them, and writing one is refused: a bare
name at type level already *is* the type constructor, so `Bool`, `none`,
`(Set t)`, `(BitVec n)` are what a type is written as.

The one place that could need the name is beneath a native the embedding gives
no name of its own, applied through `$native_apply_N`: such a place has no
declaration and so no level, and a bare name standing there would be read as a
native. No raw operator takes a type today -- the only type-valued argument one
is given is `($smtx_elem_typeof_seq_value e)`, a program call, which is the
same at any level. Should one ever need a type, the answer is to give that
native a name, the way `$native_model_lookup` is named in
`plugins/model_smt/model_smt.eo`, which is what makes its third argument a type
the compiler can see.

---

## 9. Checks

The compiler enforces, beyond the grammar:

- **Every helper is written out.** A symbol never says which helper it reaches
  for; the compiler notes what a block came to name and then checks that some
  file of the same set writes it out. This is what keeps the two halves from
  leaning on each other silently.
- **A name a case does not bind is an error**, so a misspelt argument is caught
  rather than becoming a symbol of the theory that does not exist.
- **A parameter is not declared twice as two things.**
- **A native exists and takes the right number of arguments.**
- **A type of the embedding exists.**

`--check` writes nothing, and reports:

| report | meaning |
| --- | --- |
| out-of-order uses | a block uses a name a later block defines |
| current | the generated file holds what compiling would write |
| STALE / MISSING | it does not, or has never been written; run the compiler |

A definitions file is ordered so that a symbol follows the ones its cases name.
The configuration does not state that: blocks are emitted in the order the
files read, and the order is then confirmed. A program written over values is
exempt, since the stage that reads the file forward declares every one of them
before it defines any; which programs those are is read off the aggregates'
`:helper`.

No pair of spellings is listed by hand: each constructor is folded into the
macro that applies it and each native into the name it is defined under, both
read out of the files that define them.

---

## 10. Worked examples

### A bit-vector operator

```lisp
(define-symbol bvadd (x y)
  :typeof ($smtx_typeof_bv_op_2 x y)
  :eval ((bv n x) (bv m y) -> (bv n))  ("z_+" x y))
```

compiles to

```lisp
; -- bvadd
(declare-parameterized-const $emb_sm.bvadd
  ((x1 $smt_Term :opaque) (x2 $smt_Term :opaque)) $smt_Term)
(define $sm_bvadd ((x1 $smt_Term) (x2 $smt_Term)) ($emb_sm.bvadd x1 x2))
(program $smtx_model_eval_bvadd
  ((n $native_Int) (x $native_Int) (m $native_Int) (y $native_Int)
   (t1 $smt_Value) (t2 $smt_Value))
  :signature ($smt_Value $smt_Value) $smt_Value
  (
  (($smtx_model_eval_bvadd ($vsm_binary n x) ($vsm_binary m y))
    ($vsm_binary n ($native_mod_total ($native_z_+ x y) ($native_z_pow2 n))))
  (($smtx_model_eval_bvadd t1 t2) $vsm_not_value)
  )
)
(program $eoc_typeof_bvadd
  ((x1 $smt_Term) (x2 $smt_Term))
  :signature ($smt_Term) $smt_Type
  (
  (($eoc_typeof_bvadd ($sm_bvadd x1 x2))
    ($smtx_typeof_bv_op_2 ($smtx_typeof x1) ($smtx_typeof x2)))
  )
)
(program $eoc_eval_bvadd
  ((M $smt_Model) (x1 $smt_Term) (x2 $smt_Term))
  :signature ($smt_Model $smt_Term) $smt_Value
  (
  (($eoc_eval_bvadd M ($sm_bvadd x1 x2))
    ($smtx_model_eval_bvadd ($smtx_model_eval M x1) ($smtx_model_eval M x2)))
  )
)
```

The constructor and its macro come from the shape of the target; the helper from
the `:eval` cases and the `bv` shape; the two remaining programs from the
`type` and `value` aggregates, the second by the `value` aggregate's
`:default`, since the symbol said no `:value`.

### A symbol that reaches for the model

Nothing is a projection of a signature here, so the symbol writes the case
itself. `M` is what `:context` declares, and an argument stands for its value.

```lisp
(define-symbol div (x y)
  :typeof (of2 Int Int Int x y)
  :value (eo::define ((a x)) (eo::define ((b y))
           (ite (= b 0)
             (apply M ("model_lookup" M "div_by_zero_id" (FunType Int Int)) a)
             (div_total a b)))))
```

### A symbol of the input, and its nil

```lisp
(define-symbol str.++ (s t)
  :is-list-nil (seq.empty T) true
  :is-list-nil             (eo::eq s ""))
```

compiles to

```lisp
; -- str.++
(program $eoc_transform_str.++
  ((T Type) (T1 Type) (T2 Type) (x1 T1) (x2 T2))
  :signature (T) $smt_Term
  (
  (($eoc_transform_str.++ (str.++ x1 x2))
    ($sm_str.++ ($eo_to_smt x1) ($eo_to_smt x2)))
  )
)
(program $eoc_is_list_nil_str.++
  ((T Type) (x1 T))
  :signature (T) Bool
  (
  (($eoc_is_list_nil_str.++ (seq.empty T)) true)
  (($eoc_is_list_nil_str.++ x1) (eo::eq x1 ""))
  )
)
```

The first program is the `term` aggregate's `:default`, since the symbol said
nothing about `term` and `nil` is not `:sole`. The `nil` aggregate is at level
`input`, so its bodies are emitted as written, with the entry's names put for
the parameters.

### A type constructor

```lisp
(define-symbol Seq (T)
  :type (guard T (Seq T)))
```

compiles to

```lisp
; -- Seq
(program $eoc_transform_type_Seq
  ((T1 Type) (x1 T1))
  :signature (Type) $smt_Type
  (
  (($eoc_transform_type_Seq (Seq x1))
    ($smtx_typeof_guard ($eo_to_smt_type x1) ($tsm_Seq ($eo_to_smt_type x1))))
  )
)
```

`guard` is a macro of `types.eo`; `T` stands for `($eo_to_smt_type x1)`, which
is what the `type` aggregate's `:stands-for` says; and `(Seq T)` at type level
is `$tsm_Seq`. Because `type` is `:sole`, no `term` case is also written.

---

## 11. Recipes

### Add a symbol

Write a `define-symbol` in the section of its theory, saying one case per
aggregate. On the SMT-LIB side that is a `:typeof` -- a term at type level, in
which an argument stands for its type -- and either `:eval` cases or a
`:value`. On the input side it is usually nothing at all.

If its type rule is one several symbols share, write the program once at the
top of the file and name it; if its value needs to recurse or to match values
several ways, write that program at the top of the file too, under a name of
its own -- `$smtx_repeat_rec`, the way `$smtx_map_select` is named -- and say a
`:value` that calls it by that name. The names the compiler writes are the
compiler's to write: a program written by hand under `$smtx_model_eval_<name>`
would stand where the compiler puts the program it writes for a symbol, and
would answer to a body naming a symbol that was never declared.

### Add a sort

Write a `define-sort` at the end of the types, saying what it is well-founded
on, what bounds it and what value stands for it where a model has to name one;
a type that has nothing to say about one of those says nothing. It goes at the
end because the order of the types is what their constructors are numbered by.

Nothing more is needed if the embedding already has a constructor for a value
of it: a case matches one by writing it, and what the pattern binds is read off
its declaration. If putting one back together is an idiom, write a macro for it
in the section of its theory, the way `of_width` and `of_chars` are written.

If a value of it is built over something that is neither a native nor a value
-- a list of entries, a sequence -- the type of that and the constructors that
build one are declared in `plugins/model_smt/model_smt.eo`, beside `$smt_Map`
and `$smt_Seq`; a set may not declare one, see
[Nothing else](#nothing-else). The programs over it are `program`s here, beside
the sort.

### Add a value

Write a `define-value` at the end of the values, saying each parameter's type,
the type a term of it would be of, and what makes it canonical; a value that
has nothing to say about one of those says nothing. Name the macro that applies
it in the vocabulary block, since a value has no bare name. It goes at the end
because the order of the values is what their constructors are numbered by.

### Add a literal

Write a `define-literal` at the end of the literals, saying the type of what it
carries, the type a term of it is of, and its value in a model. Write the
constructor of the value it evaluates to as well, unless the embedding already
has one. It goes at the end for the same reason a value does.

### Add an attribute a symbol may carry

Not a change to a signature: add it to the shape in `tools/eoc/sem_target.py`,
and teach `DefsFile::read` in `plugins/model_smt/defs_reader.cpp` the prefix of
the program it writes, so the stage knows what to do with its cases.

### Add a signature of another input

Write a file beside `semantics/development-cpc.eos`: a heading, then its
theories in sections. Name it with `--signature`, which is what gives it the
shape of an input, and it compiles beside itself unless it is one of the two
the tool ships with. Nothing in the compiler names either existing set.

---

## 12. Diagnostics

Every message is prefixed `sem_compile:`. The ones worth knowing:

| message | cause |
| --- | --- |
| `write X, the type constructor, rather than the macro $tsm_X` | a type written as the macro of the embedding rather than as the type it is |
| `X is named but this case does not bind it` | a body names something its own pattern did not match -- usually a misspelt argument |
| `X names Y, which no file of sem/Z writes out` | a case reaches for a helper nothing writes |
| `X declares nothing, so what a pattern of it binds cannot be read` | a pattern applied something the embedding does not declare |
| `X takes N arguments, not M` | a pattern applied something to the wrong number of arguments |
| `X is declared as A and as B` | two cases take one name apart as two different things |
| `no argument of X is K` | an aggregate's `:stands-for` says nothing about a kind of parameter the symbol used |
| `says what it matches ... before what it gives` | a helper attribute was given one value where it takes two |
| `says N patterns for M arguments` | a helper case does not match the symbol's arity |
| `says nothing, so nothing is written for it` | a symbol contributes to no aggregate |
| `write X, the macro of the embedding, rather than the constructor Y` | and the four other refusals of [Casting](#8-casting) |
| `there is no native called $native_X` | a name in quotes the embedding does not have, in a set with no value layer to forward it to |
| `$native_X takes N arguments, not M` | a native applied wrongly |
| `every case of X says what it matches` | a case gave no pattern for an aggregate whose subject is not the symbol applied to its arguments |
| `X is ..., which the compiler writes for itself` | a program written out under a name the compiler gives, e.g. `$smtx_model_eval_X`; name it as itself |
| `write X, the symbol of the signature, rather than $smtx_model_eval_X` | a body naming the program the compiler wrote for a symbol rather than the symbol |
| `X is both a macro and a symbol of this set` | a macro would shadow the symbol, since a macro is matched first |
| `X is given twice, see F` | two blocks of one name |
| `cannot tell what block X belongs to` | a form on its own whose name says nothing; open a block with a `; -- name` line |
| `X is not a form of a configuration set` | a form that is none of the above, e.g. a bare `declare-const` or `define`; a set says what a theory does, never what the embedding is |
