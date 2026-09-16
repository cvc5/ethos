# The eo-meta backend

Compiles a Eunoia signature back to Eunoia, stated over a *small* set of
primitives.

```bash
python3 tools/eoc/driver.py desugar --natives=eo \
  --semantics tools/eoc/semantics/development-cpc.eos <input.eo>
```

A signature that goes in may use any Eunoia primitive it likes. The desugar
stage rewrites all of them into the natives of the deep embedding, and this
backend then writes those natives back as Eunoia -- but only as the primitives
[`eo.eos`](eo.eos) names. What comes out therefore says what the input said
over a smaller language than the input was written in, and that smaller
language is the point: it is a different proof language, arrived at by
construction rather than by hand.

## It has no C++ of its own

The other backends -- `lean-meta`, `smt-meta` -- each read the compiled
signature and write another language, so each is a stage with a plugin behind
it. This one writes the language the stage already produces, so there is
nothing for it to do beyond saying what a native *is*: the desugar stage emits
the signature, and the natives are answered from this set instead of from
`plugins/desugar/natives.eos`. That is the whole backend.

So what lives here is one configuration set, in the same form as the native
layer of every other backend:

| Backend | Native layer | Says a native in |
| --- | --- | --- |
| `lean-meta` | `plugins/lean_meta/lean.eos` | Lean |
| `smt-meta` | `plugins/smt_meta/smt-vc.eos` | SMT-LIB |
| `eo-meta` | `plugins/eo_meta/eo.eos` | Eunoia |

## What it covers

A native this set does not name keeps the body every other backend gives it,
an application of `$native_apply_N`, which no Eunoia evaluates. So the part of
a signature this backend accounts for is the part written over the natives it
names, and widening that is adding a line to `eo.eos`.

The bit-vector natives -- the integer-pair encodings behind `binary_and` and
friends -- and the natural-number encoding are the two families it does not
name yet. Both are expressible; neither is one line.
