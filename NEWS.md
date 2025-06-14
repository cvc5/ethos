This file contains a summary of important user-visible changes.

ethos 0.2.0
===========

This release of Ethos is associated with the 1.3.0 release of the SMT solver cvc5.

- Drops support for `:var`, `:implicit`, `:requires` and `:opaque` as *term* attributes. The recommended way of introducing function symbols with named arguments is via the command `declare-parameterized-const`, which now permits the latter three as parameter annotations. The parameters of a parameterized constants are no longer assumed to be implicit, and are explicit by default.
- Change the execution semantics when a program takes an unevalated term as an argument. In particular, we do not call user provided programs and oracles when at least argument could not be evaluated. This change was made to make errors more intuitive. Note this changes the semantics of programs that previously relied on being called on unevaluated terms.
- Change the semantics of a corner case of `eo::is_eq`. In particular, `eo::is_eq` now returns false if given two syntactically equivalent terms whose evaluation is stuck. This change also impacts the semantics of `eo::requires`, which evaluates to the third argument if and only if the first two arguments are syntactically equivalent *and* are fully evaluated.
- User programs, user oracles, and builtin operators that are unapplied are now considered unevaluated. This makes the type checker more strict and disallows passing them as arguments to other programs, which previously led to undefined behavior.
- In type checking, the free parameters in the types of parameters are now also bound when that parameter is instantiated.
- Changed the semantics of pairwise and chainable operators for a single argument, which now reduces to the neutral element of the combining operator instead of a parse error.
- The operator `eo::typeof` now fails to evaluate if the type of the given term is not ground.

- Adds support for the SMT-LIB `as` annotations for ambiguous functions and constants, i.e. those whose return type cannot be inferred from their argument types. Following SMT-LIB convention, ambiguous functions and constants are expected to be annotated with their *return* type using as.  Eunoia translates this into a type argument to the function. This policy is applied both for ambiguous datatype constructors and ambiguous functions and constants declared with `declare-parameterized-const`.
- The semantics for `eo::dt_constructors` is extended for instantiated parametric datatypes. For example calling `eo::dt_constructors` on `(List Int)` returns the list containing `cons` and `(as nil (List Int))`.
- The semantics for `eo::dt_selectors` is extended for annotated constructors. For example calling `eo::dt_selectors` on `(as nil (List Int))` returns the empty list.
- To support parameteric nil terminators, the operator `eo::nil` now always requires two arguments, the list operator and the desired type for the nil terminator.

- Adds support for dependent types for programs. The argument types of programs can now use `eo::quote` to specify an input parameter to that program.

- Adds builtin operators `eo::eq` and `eo::is_ok`.
- Adds builtin list operators `eo::list_rev`, `eo::list_erase`, `eo::list_erase_all`, `eo::list_setof` (returns the unique elements of the list), `eo::list_minclude` (multiset inclusion) and `eo::list_meq` (multiset equality).
- Added the option `--stats-all` to track the number of times side conditions are invoked.
- The option `--print-let` has been renamed to `--print-dag` and is now enabled by default. The printer is changed to use `eo::define` instead of `let`.
- The option `--binder-fresh`, which specified for fresh variables to be constructed when parsing binders, has been removed.
- Programs and oracles now are explicitly required to have at least one argument.
- Remove support for the explicit parameter annotation `eo::_`, which was used to provide annotations for implicit arguments to parameterized constants.
- Programs are now recommended to use the attribute `:signature` to specify the argument and return types.

ethos 0.1.1
===========

This release of Ethos is associated with the 1.2.1 release of the SMT solver cvc5.

- When parsing Eunoia signatures, decimals and hexidecimals are never normalized, variables in binders are always unique for their name and type, and let is never treated as a builtin way of specifying macros. The options `--no-normalize-dec`, `--no-normalize-hex`, `--binder-fresh`, and `--no-parse-let` now only apply when parsing proofs and reference files.
- Adds a new option `--normalize-num`, which also only applies when reference parsing. This option treats numerals as rationals, which can be used when parsing SMT-LIB inputs in logics where numerals are shorthand for rationals.
- Makes the `set-option` command available in proofs and Eunoia files.
- Adds `--include=X` and `--reference=X` to the command line interface for including (reference) files.
- Fixed the disambiguation of overloaded symbols that are not applied to arguments.
- Fixed the interpretation of operators that combine opaque and ordinary arguments.
- Fixed a bug in the evaluation of `eo::cons` for left associative operators, which would construct erroneous terms.
- Adds support for `eo::dt_constructors` which returns the list of constructors associated with a datatype, and `eo::dt_selectors` which returns the list of selectors associated with a datatype constructor. These operators make use of a type `eo::List`, which is now part of the background signature assumed by Ethos.
- Fixed parser for the singleton case of `declare-datatype`.

ethos 0.1.0
===========

This is the initial release of the Ethos proof checker.  Ethos implements the Eunoia logical framework which is a logical framework targeted at SMT solvers.  It allows users to define proof formats and write proofs.

This release of Ethos is associated with the 1.2.0 release of the SMT solver cvc5.  It can check the proofs generated by cvc5's native proof format `cpc`.  Ethos and Eunoia have reached a certain level of stability, but they are still under active development.

## Development Repository

https://github.com/cvc5/ethos

## Documentation

https://github.com/cvc5/ethos/blob/main/user_manual.md

