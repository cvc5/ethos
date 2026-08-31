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

For the wider design context see [`README.md`](README.md) -- §10 is the same
`is_list_nil` problem from the other end, and Part IV item 1 is the change that
dissolves most of item 1 here.

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

## 1. `:whole`

**What it does.** An aggregate normally takes the *cases* out of each
per-symbol program and splices them into one program at `:into`. `:whole` emits
each program entire instead, with its case prefix rewritten to the aggregate's
name (`DefsFile::classifyProgram` in `plugins/model_smt/defs_reader.cpp`), and
keeps the marker out of `d_spliced` so what lands there is not indented as a
case. One aggregate uses it, `$eo_is_list_nil_`, whose trailing underscore is
the tell that it names a family rather than a program.

**What holds it in place.** Not the aggregate table -- the desugar stage.
`plugins/desugar/desugar.cpp` builds the name `$eo_is_list_nil_<symbol>` by
string concatenation, forward declares it into `$EO_IS_LIST_NIL_DEFS$`, and
emits a call to it. The configuration has to supply the body under exactly that
name, so the per-symbol programs cannot be merged into one. `:whole` is the
configuration's half of a name-level protocol with a C++ stage.

**Why the protocol exists at all.** Only for a symbol whose nil is *non-ground*.
Where the nil is ground the desugar stage writes `(($eo_is_list_nil f <nil>)
true)` itself and needs nothing. For `+` the nil is any rational equal to zero,
so what is wanted is a predicate, and only the configuration has it.

**What deleting it needs.** The `:is-list-nil` cases have to splice into
`$eo_is_list_nil` as ordinary cases. What stops that today is that two stages
write that one program -- the desugar stage from the `:right-assoc-nil`
attributes of a signature, the model-smt stage from the set -- into different
files at different times. So one of:

- give the desugar stage a configuration input of its own, which is Part IV
  item 1 of [`README.md`](README.md) and dissolves this along with the rest of
  §10; or
- move the `:into` marker of `$eo_is_list_nil` into the desugar template, so
  both writers land in one place. Much the smaller change, and the one to cost
  first if the larger one is not being taken.

**What not to do.** `:whole` is *nearly* derivable, since the only aggregate
that has it is the only one whose declared name ends in `_`. That is one data
point, and a trailing underscore is a poor carrier for semantics. Deleting the
keyword that way would hide the protocol rather than remove it.

**Nearby, and independent.** `optionFwdDeclIsListNilNground()` in
`plugins/desugar/desugar.cpp` is `{ return true; }` -- an option that is not
one -- and the `else` branch it guards is dead. Deleting that branch is pure
deletion and does not wait on any of the above.

---

## 2. `:helper` and `:forward`

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
