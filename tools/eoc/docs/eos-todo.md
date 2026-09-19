# Configuration work still open

The [design notes](design.md) describe the wider boundary between the compiler
and its input. This page keeps the remaining concrete configuration questions.

## Helper declarations

`:helper` and `:forward` are a pair on a model aggregate; the compiler rejects
one without the other. The value aggregate uses them to name programs that
operate on evaluated arguments and the marker where their declarations go.

The names live in `plugins/model_smt/model_smt.eos`, while `helper_attr`,
`helper_arg` and `helper_gives` live in `tools/eoc/compiler/sem_target.py`. The
two files must agree about whether the aggregate has a helper family. The choice
is whether to express the complete helper shape in configuration or keep the
complete definition in Python. Removing only the two attributes would leave
the underlying split unresolved.

## Nil predicates

`:is-list-nil` compiles to programs in `user_desugar.eo`, as declared by
`plugins/desugar/desugar.eos`. The driver inserts the programs needed by the
signature. It does not yet check coverage explicitly or prove their equivalence
to `(eo::eq (eo::nil f (eo::typeof x)) x)`.

`:whole` and `:datatype` are not configuration attributes. A desugar aggregate
already writes a separate program per symbol; backend-native type definitions
belong in each backend's native layer.
