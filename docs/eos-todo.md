# Attributes to delete from the configuration language

A working list for the corners of `.eos` that carry a fact the compiler could
carry itself, or that carry half of one. Each entry says what the attribute
does today, what is actually holding it in place, and what deleting it would
take, so that the work can be picked up without tracing it again.

These came out of an audit of every form and attribute in the language against
its uses. Most of the language came through it well: the set of forms is closed
and anything outside it is refused, the attribute vocabulary is defined by
`declare-aggregate-method` rather than hardcoded, and `:builds` together with
`declare-embed-datatype` let a datatype of the embedding be added in
configuration alone. What is below is the residue.

For the wider design context see [`README.md`](README.md) -- §10 is the
`is_list_nil` problem from the other end, and Part IV is where the changes
these entries call for are sketched.

---

## Done: `:datatype`

Deleted. It said that `<nat>` is a type a backend must be *given* rather than
one it already has, and it reached nothing.

What it did was pick `$native_datatype` over `$native_type_0` in the macro
`(define $native_Nat () (...))`, which classified the type as
`MetaKind::SMT_BUILTIN_DATATYPE` instead of `MetaKind::SMT_BUILTIN`. Following
both to the end: each of the three C++ sites testing the `$native_datatype`
prefix was a disjunction in which `$native_type_` already matched, two of the
three consumers of the meta-kind treated the pair identically, and the third
was two adjacent `switch` cases with identical bodies.

Removing it left all 600 CPC Lean modules, the verification condition and the
synthesis query byte-identical; the only thing that moved was the macro line
itself. The fact it was trying to state is carried where the text to act on it
can actually be written -- `Nat` is a `define-native-method` in
`plugins/smt_meta/smt-vc.eos` whose `:smt-impl` is the `declare-datatype`, and
the generated `.smt2` still opens with that line.

Kept as a record so it is not re-argued: the removal took the attribute, the
`$native_datatype` declaration in `plugins/desugar/native_embed.eo`, the
`SMT_BUILTIN_DATATYPE` meta-kind, and four prefix tests.

---

## Done: `:whole`, by moving `is_list_nil` to the desugar stage

Deleted, along with the reason it existed. The nil predicate of an n-ary
symbol is now compiled to a file the desugar stage reads rather than into a
hole in the model template.

**What it was.** An aggregate normally has the *cases* taken out of each
per-symbol program and spliced into one program at `:into`. `:whole` emitted
each program entire instead, renamed from the case prefix to the aggregate's
name, because `plugins/desugar/desugar.cpp` builds the name
`$eo_is_list_nil_<symbol>` and calls it. The bodies could only arrive from the
model, a later stage, so the desugar stage forward declared each and waited.

**What replaced it.** `plugins/desugar/desugar.eos` -- a configuration set for
stage 5, which is what there was none of. An aggregate declared there is
written out one program to a symbol, named for the symbol, into
`tools/eoc/out/user_desugar.eo`; the desugar template names that file with an
`(include "user_desugar.eo")` standing after the signature's own declarations
and ahead of the cases, and the driver answers it the way it already answered
`native_defs.eo`. `:is-list-nil` is still written where it was, beside the
symbol's other attributes; only the file it compiles to changed.

The include is answered with the blocks the signature *calls* rather than with
the whole file, since a run compiles one signature and it may declare none of
the nine symbols -- a program over a symbol that was trimmed away would name
what nothing declares. See `inline_called_blocks` in `tools/eoc/driver.py`.

**What went with it:**

- `$EO_DESUGAR_AUX$`, the hole in the *model* template whose only job was to
  let stage 6 fill in stage 5's, and the `d_whole` field, its branch in
  `defs_reader.cpp`, the fourth optional word of the `$eoc-aggregate` line and
  the `d_spliced` exception in `model_smt.cpp`;
- `$EO_IS_LIST_NIL_DEFS$` and the per-symbol forward declarations, the bodies
  now standing ahead of the cases that call them;
- the rename `$eoc_is_list_nil_X` to `$eo_is_list_nil_X`, and with it the only
  `$eoc_` label that survived into a generated file: the programs are written
  under their real names from the start;
- `optionFwdDeclIsListNilNground`, which returned `true` unconditionally, and
  the principled-but-dead `eo::typeof` branch it guarded.

`level='input'` remains, and should. It is what makes the body come out in the
input's own vocabulary, which is exactly right for a file the desugar stage
reads; it was an exception only while it lived in a set of model semantics.

**What did not change.** All 1121 definitions of the CPC `Logos.lean` are
present with identical bodies -- they moved in the file, since the programs are
now written in the desugar section rather than the model one, so the file is
not byte-identical. Every other generated Lean module is, and the verification
condition and the synthesis query are byte-identical.

**Still open here.** The predicate is hand-written and unverified against its
stated meaning, `(eo::eq (eo::nil f (eo::typeof x)) x)` -- Part IV item 3 of
[`README.md`](README.md), a VC per block. And nothing yet compares the symbols
the stage forward-declared a predicate for against the symbols a set wrote one
for; that check is now cheap, because both halves are in one stage, and it is
the next thing to do. See Part IV item 2.

---

## 1. `:helper` and `:forward`

**What they do.** They are a pair; the compiler refuses one without the other.
A `define-symbol` that writes no `:eval` case of its own hands its work to
`$smtx_model_eval_<symbol>`, a program written over *values* rather than over
terms. `:helper` names that prefix and `:forward` names the marker where they
are all declared ahead of the aggregate, since a case of one may name another
whichever comes first.

**What is actually wrong.** Not that they have one use each. Whether an
aggregate *has* a helper family is hardcoded: `helper_attr='eval'`, with
`helper_arg='$smt_Value'` and `helper_gives='$smt_Value'`, on the `VALUE`
aggregate in `tools/eoc/sem_target.py`. The set carries only the names. The two
halves are then checked against each other, and the diagnostic says what the
arrangement is:

> the set and sem_target.py disagree about whether the cases of this aggregate
> hand their work to a program written over values

A check whose whole job is to keep two files telling one story is the thing to
remove, and these attributes are one half of that story.

There is exactly one helper family *because the code permits exactly one*. The
configuration generalised the concept and the Python did not follow, which is
why the attributes look ephemeral when the concept is not.

**What deleting them needs.** Pick which side owns the fact:

- **Finish the move.** Put `helper_arg` and `helper_gives` into
  `declare-aggregate-method` beside `:helper` and `:forward`. A helper family
  becomes fully declarable, the consistency check goes away, and the two
  attributes stop being loose ends -- they become part of a complete
  declaration rather than the naming half of a split one. This is the direction
  the rest of the language has been going, and it is the one to take unless
  there is a reason not to.
- **Undo the move.** Put the two names into `sem_target.py` next to
  `helper_attr`. Two fewer attributes in the set, two more hardcoded names, and
  the check goes away as well. Cheaper, and against the grain.

Either way the check is what should not survive. Deleting the attributes
without deciding this would just move the hardcoding.
