# Compiler documentation index

The [compiler README](../README.md) introduces this experimental tool and its
scope. Run the commands on these pages from the Ethos repository root unless
stated otherwise.

| Document | Purpose |
| --- | --- |
| [Compiler README](../README.md) | Build, run, output layout, supported targets and limitations. |
| [Configuration reference](semantics.md) | The `.eos` language, compilation checks and examples. |
| [Proof pipeline](proof-pipeline.md) | How calculus compilation relates to checking a solver's proof. |
| [Design notes](design.md) | Current configuration boundaries and open design questions. |
| [Configuration work](eos-todo.md) | Helper-family and nil-predicate questions that remain open. |
| [Noesis readiness](noesis-readiness.md) | What a Lean semantics of Eunoia and a compiler-correctness theorem would need from this tree. |
| [Eunoia backend](../../../plugins/eo_meta/README.md) | The experimental `desugar --natives=eo` target and its coverage. |

These pages are written by hand. Files under `tools/eoc/out/` are generated
in full by the configuration compiler or driver and are not committed.
