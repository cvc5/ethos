# Introduction

This is the user manual for the AletheLF checker (alfc), an efficient and extensible tool for checking proofs of Satisfiability Modulo Theories (SMT) solvers.

## Building alfc

The source code for alfc is available here: https://github.com/cvc5/alfc.
To build alfc, run:
```
mkdir build
cd build
cmake ..
```
The `alfc` binary will be available in `build/src/`.

### Debug build

By default, the above will be a production build of `alfc`. To build a debug version of `alfc`, that is significantly slower but has assertions and trace messages enabled, run:
```
mkdir build -DCMAKE_BUILD_TYPE=Debug
cd build
cmake ..
```
The `alfc` binary will be available in `build/src/`.

## Command line interface of alfc

`alfc` can be run from the command line via:
```
alfc <option>* <file>
```
The set of available options `<option>` are given in the appendix. Note the command line interface of `alfc` expects exactly one file (which itself may reference other files via the `include` command as we will see later). The file and options can appear in any order.

The ALF checker will either emit an error message indicating:
- The kind of failure (type checking, proof checking, lexer error),
- The line and column of the failure.
Otherwise, the ALF checker will print `success` when it finished parsing all commands in the file or encounters and `exit` command.
Further output can be given by user-provided `echo` commands.

### Streaming input to the ALF checker

The `alfc` binary accepts input piped from stdin. The following are all equivalent ways of running `alfc`:
```
% alfc <file>
% alfc < <file>
% cat <file> | alfc
```

## Overview of Features

The AletheLF (ALF) language is an extension of SMT-LIB version 3.0 for defining proof rules and writing proofs from SMT solvers. Since ALF is closely based on the SMT-LIB format, ALF files typically are given the suffix `*.smt3`.

The core features of the ALF language include:
- Support for SMT-LIB version 3.0 syntax for defining theory signatures.
- Support for associating syntactic categories (as specified by SMT-LIB e.g. `<numeral>`) with types.
- A set of commands for specifying proofs (`step`, `assume`, and so on), whose syntax closely follows the Alethe proof format (for details see []).
- A command `declare-rule` for defining proof rules.

The ALF checker alfc extends this language with several features:
- A library of operations (`alf.add`, `alf.mul`, `alf.concat`, `alf.extract`) for performing computations over values.
- A command `program` for defining side conditions as ordered list of rewrite rules.
- A command `declare-oracle-fun` for user-provided oracles, that is, functions whose semantics are given by external binaries. Oracles can be used e.g. for modular proof checking.
- Commands for file inclusion (`include`) and referencing (`reference`). The latter command can be used to specify the name of an `*.smt2` input file that the proof is associated with.

In the following sections, we review these features in more detail. A full syntax for the commands is given at the end of this document.


# Declaring theory signatures

In ALF as in SMT-LIB version 3.0, a common BNF is used to specify terms, types and kinds.
In this document, a *term* may denote an ordinary term, a type or a kind.
Terms are composed of applications, built-in operators of the language (e.g. for performing computations, see [computation](#computation)), literals (see [literals](#literals)), and three kinds of atomic terms (*constants*, *variables*, and *parameters*) which we will describe in the following.
A *function* is an atomic term having a function type.
The standard `let` binder can be used for specifying terms that contain common subterms, which is treated as syntax sugar.

As mentioned, the core language of ALF does not assume any definitions of standard SMT-LIB theories.
Instead, SMT-LIB theories may defined as ALF signatures.
Specifically, the ALF language has the following builtin expressions:
- `Type`, denoting the kind of all types,
- `->`, denoting the function type,
- `_`, denoting (higher-order) function application,
- `Bool`, denoting the Boolean type,
- `true` and `false`, denoting values of type `Bool`.

> The core logic of the ALF checker also uses several builtin types (e.g. `Proof` and `Quote`) which define the semantics of proof rules. These types are intentionally left hidden from the user. Details on these types can be found throughout this document. More details on the core logic of the ALF checker can be found here [].

In the following, we informally write BNF categories `<symbol>` to denote an SMT-LIB version 3.0 symbol, `<term>` to denote an SMT-LIB term and `<type>` to denote a term whose type is `Type`, `<typed-param>` has syntax `(<symbol> <type> <attr>*)` and binds `<symbol>` as a fresh parameter of the given type and attributes (if provided).

The following commands are supported for declaring and defining types and terms. The first set of commands are identical to those in SMT-LIB version 3.0:
- `(declare-const <symbol> <type> <attr>*)` declares a constant named `<symbol>` whose type is `<type>`. Can be given an optional list of attributes (see [attributes](#attributes)).
- `(declare-fun <symbol> (<type>*) <type> <attr>*)` declares a constant named `<symbol>` whose type is given by the argument types and return type. Can be given an optional list of attributes.
- `(declare-sort <symbol> <numeral>)` declares a new type named `<symbol>` whose kind is `(-> Type^n Type)` if `n>0` or `Type` for the provided numeral `n`.
- `(declare-type <symbol> (<type>*))` declares a new type named `<symbol>` whose kind is given by the argument types and return type `Type`.
- `(define-const <symbol> <term>)` defines `<symbol>` to be the given term.
- `(define-fun <symbol> (<typed-param>*) <type> <term>)` defines `<symbol>` to be a lambda term whose arguments, return type and body and given by the command, or the body if the argument list is empty. This throws an error if the type of the body term is not the specified type.
- `(define-sort <symbol> (<symbol>*) <type>)` defines `<symbol>` to be a lambda term whose arguments are given by variables of kind `Type` and whose body is given by the return type, or the return type if the argument is empty.
- `(define-type <symbol> (<type>*) <type>)` defines `<symbol>` to be a lambda term whose kind is given
- `(declare-datatype <symbol> <datatype-dec>)` defines a datatype `<symbol>`, along with its associated constructors, selectors, discriminators and updaters.
- `(declare-datatypes (<sort-dec>^n) (<datatype-dec>^n))` defines a list of `n` datatypes for some `n>0`.
- `(reset)` removes all declarations and definitions and resets the global scope.

The ALF language contains further commands for declaring symbols that are not standard SMT-LIB version 3.0:
- `(declare-consts <lit-category> <type>)` declares the class of symbols denoted by the literal category to have the given type.
- `(define <symbol> (<typed-param>*) <term>)`, which is identical to `define-fun` but the body term is not type checked against a reference type.
- `(declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*)` declares a variable named `<symbol>` whose type is `<type>`.

> Variables are internally treated the same as constants by the ALF checker, but are provided as a separate category, e.g. for user signatures that wish to distinguish universally quantified variables from free constants. They also have a relationship with user-defined binders, see [binders](#binders), and can be accessed via the builtin operator `alf.var` (see [computation](#computation)).

> Limited cases of symbol overloading are supported, see [overloading](#overloading).

### Example: Basic Declarations

```
(declare-sort Int 0)
(declare-const c Int)
(declare-const f (-> Int Int Int))
(declare-fun g (Int Int) Int)
(declare-fun P (Int) Bool)
```

Since alfc does not assume any builtin definitions of SMT-LIB theories, definitions of standard symbols (such as `Int`) may be provided in ALF signatures. In the above example, `c` is declared to be a constant (0-ary) symbol of type `Int`. The symbol `f` is a function taking two integers and returning an integer.

Note that despite using different syntax in their declarations, the types of `f` and `g` in the above example are identical.

> In alfc, all functions are unary. In the above example, `(-> Int Int Int)` is internally treated as `(-> Int (-> Int Int))`. Correspondingly, applications of functions are curried, e.g. `(f a b)` is treated as `((f a) b)`, which in turn can be seen as `(_ (_ f a) b)` where `_` denotes higher-order function application.

### Example: Basic Definitions

```
(declare-const not (-> Bool Bool))
(define-fun id ((x Bool)) Bool x)
(define-fun notId ((x Int)) Bool (not (id x)))
```

In the example above, `not` is declared to be a unary function over Booleans. Two defined functions are given, the first being an identity function over Booleans, and the second returning the negation of the first.

Since `define-fun` commands are treated as macro definitions, in this example, `id` is mapped to the lambda term whose SMT-LIB version 3 syntax is `(lambda ((x Bool)) x)`.
Furthermore, `notId` is mapped to the lambda term `(lambda ((x Bool)) (not x))`.
In other words, the following file is equivalent to the one above after parsing:
```
(declare-const not (-> Bool Bool))
(define-fun id ((x Bool)) Bool x)
(define-fun notId ((x Int)) Bool (not x))
```

### Example: Polymorphic types

```
(declare-sort Int 0)
(declare-sort Array 2)
(declare-const a (Array Int Bool))

(define-sort IntArray (T) (Array Int T))
(declare-const b (IntArray Bool))
```

In the above example, we define the integer sort and the array sort, whose kind is `(-> Type Type Type)`.

Note the following declarations all generate terms of the same type:

```
(declare-sort Array_v1 2)
(declare-type Array_v2 (Type Type))
(declare-const Array_v3 (-> Type Type Type))
```

## The :var and :implicit annotations

The ALF language uses the SMT-LIB version 3.0 attributes `:var <symbol>` and `:implicit` in term annotations for naming arguments of functions and specifying they are implicit.

```
(declare-sort Int 0)
(declare-const eq (-> (! Type :var T) T T Bool))
(define-fun P ((x Int) (y Int)) Bool (eq Int x y))
```

The above example declares a predicate `eq` whose first argument is a type, that is given a name `T`. It then expects two terms of type `T` and returns a `Bool`. In the definition of `P`, this predicate is applied to two variables, where the type `Int` must be explicitly provided.

```
(declare-sort Int 0)
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(define-fun P ((x Int) (y Int)) Bool (= x y))
```

In contrast, the above example declares a predicate `=` where the type of the arguments is implicit (this corresponds to the SMT-LIB standard definition of equality). In the definition of `P`, the type of the arguments `Int` does not need to be provided.

We call `T` in the above definitions a *parameter*. The free parameters of the return type of an expression should be contained in at least one non-implicit argument. In particular, the following declaration is malformed, since the return type of `f` cannot be inferred from its arguments:


```
(declare-sort Int 0)
(declare-const f (-> (! Type :var T :implicit) Int T))
```

> Internally, `(! T :var t)` is syntax sugar for the type `(Quote t)` where `t` is a parameter of type `T` and `Quote` is a distinguished type of kind `(-> (! Type :var U) U Type)`. When type checking applications of functions of type `(-> (Quote t) S)`, the parameter `t` is bound to the argument the function is applied to.

> Internally, `(! T :implicit)` drops `T` from the list of arguments of the function type we are defining.

## The :requires annotation

Arguments to functions can also be annotated with the attribute `:requires (<term> <term>)` to denote a condition under which the

```
(declare-sort Int 0)
(declare-const BitVec (-> (! Int :var w :requires ((alf.is_neg w) false)) Type))
```
The above declares the integer sort and the bitvector sort that expects a non-negative integer `w`.

In detail, the first argument of `BitVec` is an integer sort, which is named `w` via `:var`.
The second annotation indicates that `(alf.is_neg w)` must evaluate to `false`, where note that `alf.is_neg` returns `true` if and only if its argument is a negative numeral (for details, see [computation](#computation)).

> Internally, `(! T :requires (t s))` is syntax sugar for `(alf.requires t s T)` where `alf.requires` is an operator that evalutes to its third argument if and only if its first two arguments are equivalent (details on this operator are given in [computation](#computation)). Furthermore, the function type `(-> (alf.requires t s T) S)` is treated as `(-> T (alf.requires t s S))`. The ALF checker rewrites all types of the former to the latter.

## <a name="attributes"></a>Declarations with attributes

The ALF language supports term annotations on parameters and declared functions, which for instance can allow the user to treat a declared function as being variadic, i.e. taking an arbitrary number of arguments. The available annotations in the ALF checker are:
- `:right-assoc` (resp. `:left-assoc`) denoting that the term is right (resp. left) associative,
- `:right-assoc-nil <term>?` (resp. `:left-assoc-nil <term>?`) denoting that the term is right (resp. left) associative with the given nil terminator,
- `:list`, denoting that the term should be treated as a list when appearing as a child of an application of a right (left) associative operator,
- `:chainable <term>` denoting that the arguments of the term are chainable using the given (binary) operator,
- `:pairwise <term>` denoting that the arguments of the term are treated pairwise using the given (binary) operator.
- `:binder <term>` denoting that the first argument of the term can be provided using a syntax for variable lists whose constructor is the one provided.

A parameter or function can be marked with at most one of the above attributes or an error is thrown.

### Right/Left associative

```
(declare-const or (-> Bool Bool Bool) :right-assoc)
(define-fun P ((x Bool) (y Bool) (z Bool)) Bool (or x y z))
(define-fun Q ((x Bool) (y Bool)) Bool (or x y))
(define-fun R ((x Bool)) (-> Bool Bool) (or x))
```

In the above example, `(or x y z)` is syntax sugar for `(or x (or y z))`.
The term `(or x y)` is not impacted by the annotation `:right-assoc` since it has fewer than 3 children.
The term `(or x)` is also not impacted by the annotation, and denotes the partial application of `or` to `x`, whose type is `(-> Bool Bool)`.

Left associative can be defined analogously:
```
(declare-const and (-> Bool Bool Bool) :left-assoc)
(define-fun P ((x Bool) (y Bool) (z Bool)) Bool (and x y z))
```
In the above example, `(and x y z)` is syntax sugar for `(and (and x y) z)`.

Note that the type for right and left associative operators is typically `(-> T T T)` for some `T`.

### <a name="assoc-nil"></a>Right/Left associative with nil terminator

ALF supports a variant of the aforementioned functionality where a (ground) nil terminator is provided.

```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(define-fun P ((x Bool) (y Bool) (z Bool)) Bool (or x y z))
(define-fun Q ((x Bool) (y Bool)) Bool (or x y))
(define-fun R ((x Bool) (y Bool)) Bool (or x))
```

In the above example, `(or x y z)` is syntax sugar for `(or x (or y (or z false)))`,
`(or x y)` is syntax sugar for `(or x (or y false))`,
and `(or x)` is syntax sugar for `(or x false)`.

The advantage of right (resp. left) associative operators nil terminators is that the terms they specify are unambiguous, in constrast to operators without nil terminators.
In particular, note the following example:

```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(define-fun P ((x Bool) (y Bool) (z Bool)) Bool (or x (or y z)))
(define-fun Q ((x Bool) (y Bool) (z Bool)) Bool (or x y z))
```

If `or` would have been marked `:right-assoc`, then the definition of both `P` and `Q` would be `(or x (or y z))` after desugaring.
In contrast, marking `or` with `:right-assoc-nil false` leads to the distinct terms `(or x (or (or y (or z false)) false))` and `(or x (or y (or z false)))` after desugaring.

Right and left associative operators with nil terminators also have a relationship with list terms (as we will see in the following section), and in computational operators.

The type for right and left associative operators with nil terminators is typically `(-> T T T)` for some `T`, where their nil terminator has type `T`.

The nil terminator of a right associative operator may involve previously declared symbols in the signature.
For example:

```
(declare-sort RegLan 0)
(declare-const re.all RegLan)
(declare-const re.inter (-> RegLan RegLan RegLan) :right-assoc-nil re.all)
```

This example defines the constant `re.all` (in SMT-LIB, this is the regular expression accepting all strings)
and the function `re.inter` (in SMT-LIB, the intersection of regular expressions), where the latter is defined to have a nil terminator
that references the free constant `re.all`.

However, when using `declare-const`, the nil terminator of an associative operator cannot depend on the parameters of the type of that function.
For example, say we wish to declare bitvector-or (`bvor` in SMT-LIB), where its nil terminator is bitvector zero for the given bitwidth.
A possible declaration is the following:
```
(declare-const bvor
    (-> (! Int :var m :implicit) (BitVec m) (BitVec m) (BitVec m))
    :right-assoc-nil ???
)
```
The nil terminator of this operator is the bitvector zero whose width is `m`.
However note that `m` is not in scope of the declaration of its nil terminator.
We instead require such declarations to be made with `declare-parameterized-const`, which we will describe later in [param-constants](#param-constants).

### List

Atomic terms can be marked with the annotation `:list`.
This annotation marks that the term should be treated as a list of arguments when it occurs as an argument of a right (left) associative operator with a nil element. Note the following example:

```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(define-fun P ((x Bool) (y Bool)) Bool (or x y))
(define-fun Q ((x Bool) (y Bool :list)) Bool (or x y))
(declare-const a Bool)
(declare-const b Bool)
(define-const Paab Bool (P a (or a b)))
(define-const Qaab Bool (Q a (or a b)))
```

In the above example, note that `or` has been marked `:right-assoc-nil false`.
As before, the definition of `P` is syntax sugar for `(or x (or y false))`.
In contrast, the definition of `Q` is simply `(or x y)`, since `y` has been marked with `:list`.
Conceptually, our definition of `P` treats `y` as the second child of an `or` term, whereas our definition of `Q` treats `y` as the *tail* of an `or` term.

Then, `P` and `Q` are both applied to the pair of arguments `a` and `(or a b)`.
In the former (i.e. `Paab`), the definition is equivalent after desugaring to `(or a (or (or a (or b false)) false))`, whereas in the latter (i.e. `Qaab`) the definition is equivalent after desugaring to `(or a (or a (or b false)))`.
In other words, the definitions of `Paab` and `Qaab` are equivalent to the terms `(or a (or a b))` and `(or a a b)` respectively prior to desugaring.

More generally, for an right-associative operator `f` with nil terminator `nil`,
the term `(f t1 ... tn)` is de-sugared based on whether each `t1 ... tn` is marked with `:list`.
- The nil terminator is inserted at the tail of the function application unless `tn` is marked as `:list`,
- If `ti` is marked as `:list` where `1<=i<n`, then `ti` is prepended to the overall application using a concatentation operation `alf.list_concat`. The semantics of this operator is provided later in [list-computation](#list-computation).

In detail, the returned term from desugaring `(f t1 ... tn)` is constructed inductively.
If `tn` is marked with `:list`, the returned term is initialized to `tn` and we process children `ti` from `i = n-1 ... 1`.
If `tn` is not marked with `:list`, the return term is initialized to the nil terminator of `f` and we process children `ti` from `i = n .. 1`.
For each term `ti` we process, the returned term `r` is updated to `(f ti r)` if `ti` is not marked with `:list`, or to `(alf.list_concat f ti r)`
if `ti` is marked with `:list`.
Examples of this desugaring are given below.

```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(define-fun test ((x Bool) (y Bool) (z Bool :list) (w Bool :list))
    (and
        (or x y)        ; (or x (or y false))
        (or x z)        ; (or x z)
        (or x z y)      ; (or x (alf.list_concat or z (or y false)))
        (or x)          ; (or x false)
        (or z)          ; z
        (or z y w x)    ; (alf.list_concat or z (or y (alf.list_concat or w (or x false)))
    ))
```

Note that in the case of `(or z)`, no application of `or` is constructed, since only one argument term is given, since it is marked with `:list`.
In contrast, `(or x)` denotes the `or` whose children are `x` and `false`.

### Chainable

```
(declare-sort Int 0)
(declare-const and (-> Bool Bool Bool) :right-assoc)
(declare-const >= (-> Int Int Bool) :chainable)
(define-fun P ((x Int) (y Int) (z Int)) Bool (>= x y z))
(define-fun Q ((x Int) (y Int)) Bool (>= x y))
```

In the above example, `(>= x y z w)` is syntax sugar for `(and (>= x y) (>= y z))`,
whereas the term `(>= x y)` is not impacted by the annotation `:chainable` since it has fewer than 3 children.

Note that the type for chainable operators is typically `(-> T T S)` for some types `T` and `S`,
where the type of its chaining operator is `(-> S S S)`, and that operator has been as variadic via some attribute (e.g. `:right-assoc`).

### Pairwise

```
(declare-sort Int 0)
(declare-const and (-> Bool Bool Bool) :right-assoc)
(declare-const distinct (-> (! Type :var T :implicit) T T Bool) :pairwise and)
(define-fun P ((x Int) (y Int) (z Int)) Bool (distinct x y z))
```
In the above example, `(distinct x y z)` is syntax sugar for `(and (distinct x y) (distinct x z) (distinct y z))`.

Note that the type for chainable operators is typically `(-> T T S)` for some types `T` and `S`,
where the type of its pairwise operator is `(-> S S S)`, and that operator has been as variadic via some attribute.

### <a name="binders"></a>Binder
```
(declare-sort Int 0)
(declare-sort @List 0)
(declare-const @nil @List)
(declare-const @cons (-> (! Type :var T :implicit) T @List @List) :right-assoc-nil @nil)
(declare-const forall (-> @List Bool Bool) :binder @cons)
(declare-fun P (Int) Bool)

(define-fun Q1 () Bool (forall ((x Int)) (P x)))
(define-fun Q2 () Bool (forall ((x Int)) (P x)))
(define-fun Q3 () Bool (forall ((y Int)) (P y)))

(define x () (alf.var "x" Int))
(define-fun Q4 () Bool (forall (@cons x) (P x)))
```
In the above example, `forall` is declared as a binder.
This indicates that the parser (optionally) accepts a variable list as the first argument when parsing applications of `forall` instead of a term.
In particular, in the last two commands, the parser accepts `(forall ((x Int)) (P x))` for the variable list containing `x`.
A variable list parsed in this way binds the symbol `x` to a variable of type `Int` when parsing the remaining arguments of `forall`, i.e. its body.
The variable list passed as the first argument to the binder is determined by applying the specified constructor (in this case `@cons`) to the list of variables, so that `(forall ((x Int)) (P x))` is syntax sugar for `(forall (@cons x) (P x))`.
The constructor specified in declarations of binders should accept a variable number of arguments, e.g. `@cons` is declared with attribute `:right-assoc-nil`.

Variables introduced when parsing binders are always the same for each (symbol, type) pair unless the option `--binder-fresh` is enabled, in which case the variable is always unique.
In particular, this means that the definitions of `Q1` and `Q2` are syntactically identical in the above example.
On the other hand, the definition `Q3` is distinct from both of these, since `y` is a distinct variable from `x`.

Furthermore, note that a binder also may accept an explicit term as its first argument.
In the above example, `Q4` has `(@cons x)` as its first argument, where `x` was explicitly defined as a variable.
This means that the definition of `Q4` is also syntactically equivalent to the definition of `Q1` and `Q2`, again assuming that `--binder-fresh` is not enabled.

## <a name="literals"></a>Literal types

The ALF language supports associating SMT-LIB version 3.0 syntactic categories with types. In detail, a syntax category is one of the following:
- `<numeral>` denoting the category of numerals `-?<digit>+`,
- `<decimal>` denoting the category of decimals `-?<digit>+.<digit>+`,
- `<rational>` denoting the category of rationals `-?<digit>+/<digit>+`,
- `<binary>` denoting the category of binary constants `#b<0|1>+`,
- `<hexadecimal>` denoting the category of hexadecimal constants `#x<hex-digit>+` where hexdigit is `[0-9] | [a-f] | [A-F]`,
- `<string>` denoting the category of string literals `"<char>*"`.

By default, decimal literals will be treated as syntax sugar for rational literals unless the option `--no-normalize-dec` is enabled.
Similarly, hexadecimal literals will be treated as syntax sugar for binary literals unless the option `--no-normalize-hex` is enabled.

In contrast to SMT-LIB version 2, note that rational values can be specified directly using the syntax `5/11, 2/4, 0/1` and so on.
Rationals are normalized so that e.g. `2/4` and `1/2` are syntactically equivalent after parsing.
Similarly, decimals are normalized so that e.g. `1.300` is syntactically equivalent to `1.3` after parsing.
Note this is independent of whether these decimal values are further normalized to rational values.
In other words, by default `1.300` is syntactically equivalent to the rational `13/10`.
Also note in contrast to SMT-LIB version 2, negative arithmetic can be provided using the syntax e.g. `-1, -10.5, -1/3` and so on, instead of `(- 1), (- 10.5), (/ (- 1) 3)`.

String values use the standard escape sequences as specified in SMT-LIB version 2.6, namely `""` within a string literal denotes `"`.
The only other escape sequences are of the form `\u{dn ...d1}` for `1<=n<=5` and `\u d4 d3 d2 d1` for hexadecimal digits `d1...d5` where `d5` is in the range `[0-2]`.

> Numeral, rational and decimal values are implemented by the arbtirary precision arithmetic library GMP.
Binary and hexadecimal values are implemented as layer on top of numeral values that tracks a bitwidth.
String values are implemented as a vector of unsigned integers whose maximum value is specified by SMT-LIB version 2.6, namely the character set corresponds to Unicode values 0 to 196607.

> Note that the user is not required to declare that `true` and `false` are values of type `Bool`. Instead, it is assumed that the syntactic category `<boolean>` of Boolean values (`true` and `false`) has been associated with the Boolean sort. In other words, `(declare-consts <boolean> Bool)` is a part of the builtin ALF signature.

### <a name="declare-consts"></a>Declaring classes of literals

The following gives an example of how to define the class of numeral constants.
```
(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-fun P ((x Int)) Bool (> x 7))
```

In the above example, the `declare-consts` command specifies that numerals (`1`, `2`, `3`, and so on) are constants of type `Int`.
The signature can now refer to arbitrary numerals in definitions, e.g. `7` in the definition of `P`.

> Internally, the command above only impacts the type rule assigned to numerals that are parsed. Furthermore, the ALF checker internally distinguishes whether a term is a numeral value, independently of its type, for the purposes of computational operators (see [computation](#computation)).

> For specifying literals whose type rule varies based on the content of the constant, the ALF language uses a distinguished variable `alf.self` which can be used in `declare-consts` definitions. For an example, see the type rule for SMT-LIB bit-vector constants, described later in [bv-literals](#bv-literals).

# <a name="computation"></a>Computational Operators in alfc

The ALF checker has builtin support for computations over all syntactic categories of SMT-LIB version 3.0.
We list the operators below, roughly categorized by domain.
However, note that the operators are polymorphic and in some cases can be applied to multiple syntactic categories.
For example, `alf.add` returns the result of adding two integers or rationals, but also can be used to add binary constants (integers modulo a given bitwidth).
Similarly, `alf.concat` returns the result of concatenating two string literals, but can also concatenate binary constants.
We remark on the semantics in the following.

In the following, we say a term is *ground* if it contains no parameters as subterms.
We say an *arithmetic value* is a numeral, decimal or rational value.
We say a *bitwise value* is a binary or hexadecimal value.
A 32-bit numeral value is a numeral value between `0` and `2^32-1`.
Binary values are considered to be in little endian form.

Some of the following operators can be defined in terms of the other operators.
For these operators, we provide the equivalent formulation.
A signature defining these files can be found in [non-core-eval](#non-core-eval).
Note however that the evaluation of these operators is handled by more efficient methods internally in the ALF checker, that is, they are not treated as syntax sugar internally.

Core operators:
- `(alf.is_eq t1 t2)`
    - Returns `true` if `t1` is (syntactically) equal to `t2`, or `false` if `t1` and `t2` are distinct and ground. Otherwise, it does not evaluate.
- `(alf.ite t1 t2 t3)`
    - Returns `t2` if `t1` evaluates to `true`, `t3` if `t2` evaluates to `false`, and is not evaluated otherwise. Note that the branches of this term are only evaluated if they are the return term.
- `(alf.requires t1 t2 t3)`
    - Returns `t3` if `t1` is (syntactically) equal to `t2`, and is not evaluated otherwise.
- `(alf.hash t1)`
    - If `t1` is a ground term, this returns a numeral that is unique to `t1`.
- `(alf.typeof t1)`
    - If `t1` is a ground term, this returns the type of `t1`.
- `(alf.nameof t1)`
    - If `t1` is a ground constant or variable, this returns the name of `t1`, i.e. the string corresponding to the symbol it was declared with.
- `(alf.var t1 t2)`
    - If `t1` is a string value and `t2` is ground type, this returns the variable whose name is `t1` and whose type is `t2`.
- `(alf.cmp t1 t2)`
    - Equivalent to `(alf.is_neg (alf.add (alf.neg (alf.hash t1)) (alf.hash t2)))`.
- `(alf.is_z t)`
    - Equivalent to `(alf.is_eq (alf.to_z t) t)`.
- `(alf.is_q t)`
    - Equivalent to `(alf.is_eq (alf.to_q t) t)`. Note this returns false for decimal literals when `--no-normalize-dec` is enabled.
- `(alf.is_bin t)`
    - Equivalent to `(alf.is_eq (alf.to_bin (alf.len t) t) t)`. Note this returns false for hexadecimal literals  when `--no-normalize-hex` is enabled.
- `(alf.is_str t)`
    - Equivalent to `(alf.is_eq (alf.to_str t) t)`.
- `(alf.is_bool t)`
    - Equivalent to `(alf.or (alf.is_eq t true) (alf.is_eq t false))`.
- `(alf.is_var t)`
    - Equivalent to `(alf.is_eq (alf.var (alf.nameof t) (alf.typeof t)) t)`.

Boolean operators:
- `(alf.and t1 t2)`
    - Boolean conjunction if `t1` and `t2` are Boolean values (`true` or `false`).
    - Bitwise conjunction if `t1` and `t2` are bitwise values of the same category.
- `(alf.or t1 t2)`
    - Boolean disjunction if `t1` and `t2` are Boolean values.
    - Bitwise disjunction if `t1` and `t2` are bitwise values of the same category.
- `(alf.xor t1 t2)`
    - Boolean xor if `t1` and `t2` are Boolean values.
    - Bitwise xor if `t1` and `t2` are bitwise values of the same category.
- `(alf.not t1)`
    - Boolean negation if `t1` is a Boolean value.
    - Bitwise negation if `t1` is a bitwise values of the same category.
    
Arithmetic operators:
- `(alf.add t1 t2)`
    - If `t1` and `t2` are arithmetic values of the same category, then this returns the addition of `t1` and `t2`, which is a rational value if either of `t1, t2` is a rational value, or a numeral value otherwise.
    - If `t1` and `t2` are bitwise values of the same category and bitwidth, this returns the binary value corresponding to their (unsigned) addition modulo their bitwidth.
- `(alf.mul t1 t2)`
    - If `t1` and `t2` are arithmetic values of the same category, then this returns the multiplication of `t1` and `t2`, which is a rational value if either of `t1, t2` is a rational value, or a numeral value otherwise.
    - If `t1` and `t2` are bitwise values of the same category and bitwidth, this returns the binary value corresponding to their (unsigned) multiplication modulo their bitwidth.
- `(alf.neg t1)`
    - If `t1` is a arithmetic value, this returns the arithmetic negation of `t1`.
    - If `t1` is a binary value, this returns its (signed) arithmetic negation.
- `(alf.qdiv t1 t2)`
    - If `t1` and `t2` are values and `t2` is non-zero, then this returns the rational division of `t1` and `t2`.
- `(alf.zdiv t1 t2)`
    - If `t1` and `t2` are numeral values and `t2` is non-zero, then this returns the integer division (floor) of `t1` and `t2`.
    - If `t1` and `t2` are bitwise values of the same category and bitwidth, then this returns their (total, unsigned) division, where division by zero returns the max unsigned value.
- `(alf.zmod t1 t2)`
    - If `t1` and `t2` are numeral values and `t2` is non-zero, then this returns the integer remainder of `t1` and `t2`.
    - If `t1` and `t2` are bitwise values of the same category and bitwidth, then this returns their (total, unsigned) remainder, where remainder by zero returns `t1`.
- `(alf.is_neg t1)`
    - If `t1` is an arithmetic value, this returns `true` if `t1` is strictly negative and `false` otherwise. Otherwise, this operator is not evaluated.
- `(alf.gt t1 t2)`
    - Equivalent to `(alf.is_neg (alf.add (alf.neg t1) t2))`.

String operators:
- `(alf.len t1)`
    - Binary length (bitwidth) if `t1` is a binary value.
    - String length if `t1` is a string value.
- `(alf.concat t1 t2)`
    - The concatenation of bits if `t1` and `t2` are binary values.
    - The concatenation of strings if `t1` and `t2` are string values.
- `(alf.extract t1 t2 t3)`
    - If `t1` is a binary value and `t2` and `t3` are numeral values, this returns the binary value corresponding to the bits in `t1` from position `t2` through `t3` if `0<=t2`, or the empty binary value otherwise.
    - If `t1` is a string value and `t2` and `t3` are numeral values, this returns the string value corresponding to the characters in `t1` from position `t2` through `t3` inclusive if `0<=t2`, or the empty string value otherwise.
- `(alf.find t1 t2)`
    - If `t1` and `t2` are string values, this returns a numeral value corresponding to the first index (left to right) where `t2` occurs as a substring of `t1`, or the numeral value `-1` otherwise.
    
Conversion operators:
- `(alf.to_z t1)`
    - If `t1` is a numeral value, return `t1`.
    - If `t1` is a rational value, return the numeral value corresponding to the floor of `t1`.
    - If `t1` is a binary value, this returns the numeral value corresponding to `t1`.
    - If `t1` is a string value of length one, this returns the code point of its character.
- `(alf.to_q t1)`
    - If `t1` is a rational value, return `t1`.
    - If `t1` is a numeral value, this returns the (integral) rational value that is equivalent to `t1`.
- `(alf.to_bin t1 t2)`
    - If `t1` is a 32-bit numeral value and `t2` is a binary value, this returns a binary value whose value is `t2` and whose bitwidth is `t1`.
    - If `t1` is a 32-bit numeral value and `t2` is a numeral value, return the binary value whose value is `t2` (modulo `2^t1`) and whose bitwidth is `t1`.
- `(alf.to_str t1)`
    - If `t1` is a string value, return `t1`.
    - If `t1` is a numeral value specifying a code point from Unicode planes `0-2` (i.e. a numeral between `0` and `196607`), return the string of length one whose character has code point `t1`.
    - If `t1` is a rational or binary value, return the string value corresponding to the result of printing `t1`. 
    - If `t1` is a hexadecimal value, return the string value corresponding to the result of printing `t1`. This will use lowercase letters for digits greater than `9`.
    - If `t1` is a decimal value, return the string value corresponding to the result of printing `t1` as a rational.

The ALF checker eagerly evaluates ground applications of computational operators.
In other words, the term `(alf.add 1 1)` is syntactically equivalent in all contexts to `2`.

Currently, apart from applications of `alf.ite`, all terms are evaluated bottom-up.
This means that e.g. in the evaluation of `(alf.or A B)`, both `A` and `B` are always evaluated even if `A` evaluates to `true`.

The ALF checker supports extensions of `alf.and, alf.or, alf.xor, alf.add, alf.mul, alf.concat` to an arbitrary number of arguments `>=2`.

### Computation Examples

```
(alf.and true false)        == false
(alf.and #b1110 #b0110)     == #b0110
(alf.or true false)         == true
(alf.xor true true)         == false
(alf.xor #b111 #b011)       == #b100
(alf.not true)              == false
(alf.not #b1010)            == #b0101
(alf.add 1 1)               == 2
(alf.add 1 1 1 0)           == 3
(alf.add 1/2 1/3)           == 5/6
(alf.add 2 1/3)             == (alf.add 2 1/3)  ; no mixed arithmetic
(alf.add 2/1 1/3)           == 7/3
(alf.add 2.0 1/3)           == 7/3  ; with default options
(alf.add 2.0 1/3)           == (alf.add 2.0 1/3)  ; if --no-normalize-dec is enabled, since no mixed arithmetic
(alf.add 2.0 2.5)           == 4.5  ; which is not syntactically equal to 9/2 if --no-normalize-dec is enabled
(alf.add #b01 #b01)         == #b10
(alf.add #x1 #b0001)        == #b0002  ; with default options
(alf.add #x1 #b0001)        == (alf.add #x1 #b0001)  ; if --no-normalize-hex is enabled
(alf.mul 2 7)               == 14
(alf.mul 2 2 7)             == 28
(alf.mul 1/2 1/4)           == 1/8
(alf.neg -15)               == 15
(alf.qdiv 12 6)             == 3/1
(alf.qdiv 7 2)              == 7/2
(alf.qdiv 7/1 2/1)          == 7/2
(alf.qdiv 7.0 2.0)          == 7/2  ; regardless of whether --no-normalize-dec is enabled
(alf.qdiv 7 0)              == (alf.qdiv 7 0)  ; no division by zero
(alf.zdiv 12 3)             == 4
(alf.zdiv 7 2)              == 3
(alf.is_neg 0)              == false
(alf.is_neg -7/2)           == true
(alf.len "abc")             == 3
(alf.len """hi""")          == 4
(alf.len "\u{AB0E}")        == 1
(alf.len "\uA")             == 3
(alf.len #b11100)           == 5
(alf.concat "abc" "def")    == "abcdef"
(alf.concat #b000 #b11)     == #b00011
(alf.extract "abcdef" 0 1)  == "ab"
(alf.extract "abcdef" -1 3) == ""
(alf.extract "abcdef" 1 10) == "bcdef"
(alf.extract #b11100 2 4)   == #b111
(alf.extract #b11100 2 1)   == #b
(alf.extract #b111000 1 10) == #b11100
(alf.extract #b10 -1 2)     == #b
(alf.find "abc" "bc")       == 1
(alf.find "abc" "")         == 0
(alf.find "abcdef" "g")     == -1
(alf.to_z 3/2)              == 1
(alf.to_z 45)               == 45
(alf.to_z "A")              == 65
(alf.to_z "1")              == 49
(alf.to_z "451")            == (alf.to_z "451")  ; string is not length one
(alf.to_z "")               == (alf.to_z "")  ; string is not length one
(alf.to_z "\u{9876}")       == 9876
(alf.to_q 6)                == 6/1
(alf.to_bin 4 3)            == #b0011
(alf.to_bin 4 #b1)          == #b0001
(alf.to_bin 2 #b10101010)   == #b10
(alf.to_str 65)             == "A"
(alf.to_str 123)            == "{"
(alf.to_str -1)             == (alf.to_str -1) ; since not a valid code point
(alf.to_str 200000)         == (alf.to_str 200000) ; since not a valid code point
(alf.to_str 1/2)            == "1/2"
(alf.to_str #b101)          == "#b101"
```

### Core Computation Examples

Note the following examples of core operators for the given signature

```
(declare-sort Int 0)
(declare-const x Int)
(declare-const y Int)
(declare-const a Bool)
;;
(alf.is_eq 0 1)                         == false
(alf.is_eq x y)                         == false
(alf.is_eq x x)                         == true
(alf.requires x 0 true)                 == (alf.requires x 0 true)  ; x and 0 are not syntactically equal
(alf.requires x x y)                    == y
(alf.requires x x Int)                  == Int
(alf.ite false x y)                     == y
(alf.ite true Bool Int)                 == Bool
(alf.ite a x x)                         == (alf.ite a x x)  ; a is not a value

(alf.is_eq 2 (alf.add 1 1))             == true
(alf.is_eq x (alf.requires x 0 x))      == false
(alf.ite (alf.is_eq x 1) x y)           == y
```

In the above, it is important to note that `alf.is_eq` is a check for syntactic equality after evaluation.
It does not require that its arguments denote values, so for example `(alf.is_eq x y)` returns `false`.

## <a name="list-computation"></a> List computations

Below, we assume that `f` is right associative operator with nil terminator `nil` and `t1, t2` are ground. Otherwise, the following operators do not evaluate.
We describe the evaluation for right associative operators; left associative evaluation is defined analogously.
We say that a term is an `f`-list with children `t1 ... tn` if it is of the form `(f t1 ... tn)` where `n>0` or `nil` if `n=0`.

List operators:
- `(alf.nil f)`
    - If `f` is a right associative operator, return its nil terminator.
- `(alf.cons f t1 t2)`
    - If `t2` is an `f`-list, then this returns the term `(f t1 t2)`.
- `(alf.list_len f t)`
    - If `t` is an `f`-list with children `t1 ... tn`, then this returns `n`.
- `(alf.list_concat f t1 t2)`
    - If `t1` is an `f`-list with children `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, this returns `(f t11 ... t1n t21 ... t2m)` if `n+m>0` and `nil` otherwise. Otherwise, this operator does not evaluate.
- `(alf.list_nth f t1 t2)`
    - If `f` is a right associative operator with nil terminator with nil terminator `nil`, `t1` is `(f s0 ... s{n-1})`, and `t2` is a numeral value such that `0<=t2<n`, then this returns `s_{t2}`. Otherwise, this operator does not evaluate.
- `(alf.list_find f t1 t2)`
    - If `f` is a right associative operator with nil terminator with nil terminator `nil` and `t1` is `(f s0 ... s{n-1})`, then this returns the smallest numeral value `i` such that `t2` is syntactically equal to `si`, or `-1` if no such `si` can be found. Otherwise, this operator does not evaluate.

### List Computation Examples

The terms on both sides of the given evaluation are written in their form prior to desugaring, where recall that e.g. `(or a)` after desugaring is `(or a false)` and `(or a b)` is `(or a (or b false))`.

```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
(declare-const a Bool)
(declare-const b Bool)

(alf.nil or)                  == false
(alf.nil a)                   == (alf.nil a)                ; since a is not an associative operator

(alf.cons or a (or a b))            == (or a a b)
(alf.cons or false (or a b))        == (or false a b)
(alf.cons or (or a b) (or b))       == (or (or a b) b)
(alf.cons or false false)           == (or false)
(alf.cons or a b)                   == (alf.cons or a b)                ; since b is not an or-list
(alf.cons or a (or b))              == (or a b)
(alf.cons and (or a b) (and b))     == (and (or a b) b)
(alf.cons and true (and a))         == (and a)
(alf.cons and (and a) true)         == (and (and a))

(alf.list_len or (or a b))          == 2
(alf.list_len or (or (or a a) b))   == 2
(alf.list_len or false)             == 0
(alf.list_len or (and a b))         == (alf.list_len or (and a b))  ; since (and a b) is not an or-list

(alf.list_concat or false false)            == false
(alf.list_concat or (or a b) (or b))        == (or a b b)
(alf.list_concat or (or (or a a)) (or b))   == (or (or a a) b)
(alf.list_concat or false (or b))           == (or b)
(alf.list_concat or (or a b b) false)       == (or a b b)
(alf.list_concat or a (or b))               == (alf.list_concat or a (or b))         ; since a is not an or-list
(alf.list_concat or (or a) b)               == (alf.list_concat or (or a) b)         ; since b is not an or-list
(alf.list_concat or (or a) (or b))          == (or a b)
(alf.list_concat or (and a b) false)        == (alf.list_concat or (and a b) false)  ; since (and a b) is not an or-list

(alf.list_nth or (or a b a) 1)           == b
(alf.list_nth or (or a) 0)               == a
(alf.list_nth or false 0)                == (alf.list_nth or false 0)         ; since false has <=0 children
(alf.list_nth or (or a b a) 3)           == (alf.list_nth or (or a b a) 3)    ; since (or a b a) has <=3 children
(alf.list_nth or (and a b b) 0)          == (alf.list_nth or (and a b b) 0)   ; since (and a b b) is not an or-list

(alf.list_find or (or a b a) b)          == 1
(alf.list_find or (or a b a) true)       == -1
(alf.list_find or (and a b b) a)         == (alf.find or (and a b b) a)      ; since (and a b b) is not an or-list
```

### Nil terminator with additional arguments

As we will introduce in [param-constants](#param-constants),
`alf.nil` is overloaded to accept addition arguments beyond the operator.
In particular, `(alf.nil or a b)` intuitively denotes the nil terminator
for the term `or` applied to arguments `a,b`.

### Example: Type rule for BitVector concatentation

```
(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-type BitVec (Int))

(declare-const concat (->
  (! Int :var n :implicit)
  (! Int :var m :implicit)
  (BitVec n)
  (BitVec m)
  (BitVec (alf.add n m))))

(declare-fun x () (BitVec 2))
(declare-fun y () (BitVec 3))
(define-fun z () (BitVec 5) (concat x y))
```

Above, we define a type declaration for `BitVec` that expects an integer (i.e. denoting the bitwidth) as an argument.
Then, a type rule is given for bitvector concatenation `concat`, involves the result of invoking `alf.add` on the bitwidth of its two arguments.

Since `alf.add` only evaluates on numeral values, this means that this type rule will only give the intended result when the bitwidth arguments to this function are concrete.
If on the other hand we defined:
```
...
(declare-const a Int)
(declare-const b Int)
(declare-fun x2 () (BitVec a))
(declare-fun y2 () (BitVec b))
(define z2 () (concat x2 y2))
```
The type `z2` in the above example is `(BitVec (alf.add a b))`, where the application of `alf.add` does not evaluate.
Although the above term does not lead to a type checking error, further use of `z2` would lead to errors if given as an argument to a function that did not expect this type verbatim.
For example, given a function `f` of type `(-> (BitVec (alf.add b a)) T)`, the term `(f z2)` is not well-typed, since `(alf.add a b)` is not syntactically equal to `(alf.add b a)`.

### <a name="bv-literals"></a>Example: Type rule for BitVector constants

```
(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-type BitVec (Int))

(declare-consts <binary> (BitVec (alf.len alf.self)))

(define-const x (BitVec 3) #b000)
```
To define the class of binary values, whose type depends on the number of bits they contain, the ALF checker provides support for a distinguished parameter `alf.self`.
The type checker for values applies the substitution mapping `alf.self` to the term being type checked.
This means that when type checking the binary constant `#b0000`, its type prior to evaluation is `(BitVec (alf.len #b0000))`, which evaluates to `(BitVec 4)`.

## <a name="param-constants"></a>Parameterized constants

Recall that in [assoc-nil](#assoc-nil), when using `declare-const` to define associative operators with nil terminators, it is not possible to have the nil terminator for that operator depend on its type parameters.
In this section, we introduce a new command `declare-parameterized-const` which overcomes this limitation.
Its syntax is:
```
(declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*)
```

In the following example,
we declare bitvector-or (`bvor` in SMT-LIB) where its nil terminator is bitvector zero for the given bitwidth.
```
(declare-sort Int 0)
(declare-consts <numeral> Int)                ; numeral literals denote Int constants
(declare-type BitVec (Int))
(declare-consts <binary> 
    (BitVec (alf.len alf.self)))              ; binary literals denote BitVec constants of their length
(define bvzero ((m Int)) (alf.to_bin m 0))    ; returns the bitvector value zero for bitwidth m

(declare-parameterized-const bvor ((m Int))   ; bvor is parameterized by a bitwidth m
    (-> (BitVec m) (BitVec m) (BitVec m))
    :right-assoc-nil (bvzero m)               ; its nil terminator depends on m
)
```
In this example, we first declare the `Int` and `BitVec` sorts, and associate numeral and binary values with those sorts (see [declare-consts](#declare-consts)).
Then, we declare `bvor` using `declare-parameterized-const` where its parameter is an integer `m`.
The provided parameters are in scope for the remainder of the command, which means they can appear in the nil terminator of the operator.
Here, we specify `(bvzero m)` as the nil terminator for `bvor`.

The parameter list of a parameterized constant are treated as *implicit* arguments.
In this example, the type of `bvor` is `(-> (! Int :var m :implicit) (BitVec m) (BitVec m) (BitVec m))`.

If a function `f` is given a nil terminator with free parameters, this impacts:
- How applications of `f` are desugared, and
- How list operations such as `alf.nil`, `alf.cons`, and `alf.list_concat` are computed for `f`.

For the former, say we apply `(f t1 ... tn)`, where `f` is right associative with nil terminator `nil`, where `nil` has free paramters `u1 ... um`.
Similar to the procedure described in [assoc-nil](#assoc-nil), if `tn` is not marked with `:list`, we insert the nil terminator of `f` to the end of the argument list.
To compute the parameters of the nil terminator, we first compute the type of `f` applied to arguments `t1 ... tn`.
If successful, this is the type `T [v1 ... vm / u1 ... um]` for some terms `v1 ... vm` and the given return type `T` of `f`.
If any of `v1 ... vm` is non-ground, or if the application fails to type check,
the nil terminator is `(alf.nil f t1 ... tn)`.
In other words, the computation of the nil terminator is deferred to this term (which itself may not evaluate).
Otherwise, the nil terminator is `nil[ v1 ... vm / u1 ... um]`.
Constructing `(f t1 ... tn)` then proceeds inductively via the same procedure described in [assoc-nil](#assoc-nil).
Examples of this are given in the following, assuming the declaration of `bvor` above.
```
(declare-const p (-> Bool Bool))
(define test ((x (BitVec 4)) (y (BitVec 4)) (n Int) (z (BitVec n)) (w (BitVec n)) (u (BitVec n) :list))
    ...
    (bvor x y)        ; (bvor x (bvor y #b0000))
    (bvor x)          ; (bvor x #b0000)
    (bvor z w)        ; (bvor z (bvor w (alf.nil bvor z w)))
    (bvor z u)        ; (bvor z u)
    (bvor u z)        ; (alf.list_concat bvor u (bvor z (alf.nil bvor u z)))
    ...
)
```
Above, notice that `x` and `y` have concrete bitwidths and `z,w,u` have the free parameter `n` as their bitwidth.
In the first term, `(bvor x y)` is type checked to `(BitVec m)[4/m]`.
Since `4` is ground, we compute the nil terminator `(bvzero 4)`, which evaluates to `#b0000`.
This is then used as the nil terminator, since `y` is not marked with `:list`.
The second example is similar.

In the third, example, `(bvor z w)` is type checked to `(BitVec m)[n/m]`, where note that `n` is *not* ground.
Thus, we do not compute its nil terminator and instead construct the placeholder `(alf.nil bvor z w)`.
This is then used as the nil terminator since `w` is not marked as `:list`.
In the fourth example, `(bvor z u)` is also type checked to `(BitVec m)[n/m]`, but in this case the nil terminator is not used since `u` is marked as `:list`.
In the fifth example, we use `alf.list_concat` as before since the list term `u` appears as the first argument.
Similar to the third example, a placeholder for the nil terminator is generated.

Any list operation involving `f` first requires computing the nil terminator in question.
This is done using the same procedure as described above.
If we do not infer a ground nil terminator, then the term does not evaluate.
Examples can be found at the end of this section.

Consider again the term `(bvor z w)` from the previous example:
```
(define test ((n Int) (z (BitVec n)) (w (BitVec n)))
    (bvor z w)        ; (bvor z (bvor w (alf.nil bvor z w)))
)
(declare-const a (BitVec 4))
(declare-const b (BitVec 4))
(define test4 () (test 4 a b))
```
The term in the body of `test` desugars to `(bvor z (bvor w (alf.nil bvor z w)))`, where
`(alf.nil bvor z w)` does not evaluate since the nil terminator of `(bvor z w)` involves a non-ground parameter `n`.
In this example, we instantiate this definition in the body of `test4`, where `n=4`, `z=a` and `w=b`.
The term `(bvor a (bvor b (alf.nil bvor a b)))` then evaluates to `(bvor a (bvor b #b0000)`, since the nil terminator of `(bvor a b)` has ground parameter `n=4` and evaluates to `#b0000`.

> Alternatively, the parameters of a function `f` may be provided explicitly using the syntax `(alf._ f p1 ... pn)`.
When parameters are provided, these are used instead of the type inference method above.
Furthermore, these parameters are dropped when applying the operator to arguments.
For example `(_ (alf._ bvor 4) a b)` is equivalent to `(bvor a (bvor b #b0000))` after desugaring.
An example use case for this feature is directly refer to the nil terminator of a concrete instance of `bvor`, e.g. `(alf.nil (alf._ bvor 4))` evaluates to `#b0000`.

The following are examples of list operations when using parameterized constant `bvor`:
```
(declare-const a (BitVec 4))
(declare-const b (BitVec 4))
(declare-const c (BitVec 5))

(alf.nil bvor)                == (alf.nil bvor)     ; since we cannot infer the type of bvor
(alf.nil bvor a)              == #b0000             ; since #b0000 is the nil terminator of (bvor a)
(alf.nil bvor a c)            == (alf.nil bvor a c) ; since (bvor a c) is ill-typed
(alf.nil (alf._ bvor 4))      == #b0000

(alf.cons bvor a #b0000)            == (bvor a)
(alf.cons bvor c #b0000)            == (alf.cons bvor c #b0000) ; since (bvor c #b0000) is ill-typed
(alf.cons bvor a (bvor a b))        == (bvor a a b)

(alf.list_concat bvor #b0000 #b0000)       == #b0000
(alf.list_concat bvor (bvor a b) (bvor b)) == (bvor a b b)
```

> If no free parameters are used in the nil terminator of a parameterized constant, then it is treated equivalent to if it were declared via an ordinary declare-const command, and a warning is issued.

## <a name="overloading"></a>Overloading

The ALF checker supports limited cases of overloading where all instances of the overloaded symbol have distinct arity.
In particular the following is accepted:
```
(declare-const - (-> Int Int))
(declare-const - (-> Int Int Int))
```
When parsing a term whose head is `-`, the ALF checker will automatically choose which symbol to use based on the number of arguments passed to it, e.g. `(- 1)` uses the first, and `(- 0 1)` uses the second.
If a symbol is unapplied, then the ALF checker will interpret it as the first declared term for that symbol.

Furthermore, the ALF checker supports an operator `alf.as` for disambiguation whose syntax is `(alf.as <term> <type>)`.
A term of the form `(alf.as t (-> T1 ... Tn T))` evaluates to `t` only if `(t k1 ... kn)` has type `T` where `k1 ... kn` are variables of type `T1 ... Tn`.
Otherwise, the term `(alf.as t (-> T1 ... Tn T))` is unevaluated.

# Declaring Proof Rules

The ALF language supports a command `declare-rule` for defining proof rules. Its syntax is given by:
```
(declare-rule <symbol> (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? :conclusion <term>)
where
<assumption>    ::= :assumption <term>
<premises>      ::= :premises (<term>*) | :premise-list <term> <term>
<arguments>     ::= :args (<term>*)
<reqs>          ::= :requires ((<term> <term>)*)
```

A proof rule begins by defining a list of free parameters, followed by 4 optional fields and a conclusion term.
These fields include:
- `<premises>`, denoting the premise patterns of the proof rule. This is either a list of formulas (via `:premises`) or the specification of list of premises via (via `:premise-list`), which will be described in detail later.
- `<arguments>`, denoting argument patterns of provide to a proof rule.
- `<reqs>`, denoting a list of pairs of terms.

Proof rules with assumptions `<assumption>` are used in proof with local scopes and will be discussed in detail later.

At a high level, an application of a proof rule is given a concrete list of (premise) proofs, and a concrete list of (argument) terms.
A proof rule checks if a substitution `S` can be found such that:
- The formulas proven by the premise proofs match provided premise patterns under substitution `S`,
- The argument terms match the provided argument patterns under substitution `S`,
- The requirements are *satisfied* under substitution `S`, namely, each pair of terms in the requirements list evaluates pairwise to the same term.
If these criteria are met, then the proof rule proves the result of applying `S` to the conclusion term.

A proof rule is only well defined if the free parameters of the requirements and conclusion term are also contained in the arguments and premises.

> Internally, proofs can be seen as terms whose type is given by a distinguished `Proof` type. In particular, `Proof` is a type whose kind is `(-> Bool Type)`, where the argument of this type is the formula that is proven. For example, `(Proof (> x 0))` is the proof that `x` is greater than zero. By design, the user cannot declare terms involving type `Proof`. Instead, proofs can only be constructed via the commands `assume` and `step` as we describe in [proofs](#proofs).

### Example rule: Reflexivity of equality

```
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-rule refl ((T Type) (t T))
    :premises ()
    :args (t)
    :conclusion (= t t)
)
```

The above example defines the rule for reflexivity of equality.
First a parameter list is provided that introduces a type `T` and a term `t` of that type.
The rule takes no premises, a term `t` and proves `(= t t)`.
Notice that the type `T` is a part of the parameter list and not explicitly provided as an argument to this rule.

### Example rule: Symmetry of Equality

```
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-rule symm ((T Type) (t T) (s T))
    :premises ((= t s))
    :conclusion (= s t)
)
```

This rule specifies symmetry of equality. This rule takes as premise an equality `(= t s)` and no arguments.
In detail, an application of this proof rule for premise proof `(= a b)` for concrete terms `a,b` will compute the substitution `{ t -> a, s -> b }` and apply it to the conclusion term to obtain `(= b a)`.

## Requirements

A list of requirements can be given to a proof rule.

```
(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-fun >= (Int Int) Bool)
(declare-rule leq-contra ((x Int))
    :premise ((>= x 0))
    :requires (((alf.is_neg x) true))
    :conclusion false)
```

This rule expects an arithmetic inequality.
It requires that the left hand side of this inequality `x` is a negative numeral, which is checked via the requirement `:requires (((alf.is_neg x) true))`.

## Premise lists

A rule can take an arbitrary number of premises via the syntax `:premise-list <term> <term>`. For example:

```
(declare-fun and (-> Bool Bool Bool) :right-assoc-nil true)
(declare-rule and-intro ((F Bool))
    :premise-list F and
    :conclusion F)
```
This syntax specifies that the number of premises that are provided to this rule are arbitrary.
When applying this rule, the formulas proven to this rule (say `F1 ... Fn`) will be collected and constructed as a single formula via the provided operator (`and`), and subsequently matched against the premise pattern `F`.
In particular, in this case `F` is bound to `(and F1 ... Fn)`.
The conclusion of the rule returns `F` itself.

Note that the type of functions provided as the second argument of `:premise-list` should be operators that are marked to take an arbitrary number of arguments, that is those marked e.g. with `:right-assoc-nil` or `:chainable`.

## Axioms

The ALF language supports a command `declare-axiom` which is a more concise way to specify proof rules taking no premises:
```
(declare-axiom <symbol> (<typed-param>*) <reqs>? <term>)
<reqs>  ::= :requires ((<term> <term>)*)
```
The command
```
(declare-axiom S ((x1 T1) .. (xn Tn)) R? t)
```
is syntax sugar for
```
(declare-rule S ((x1 T1) ... (xn Tn)) :args (x1 ... xn) R? :conclusion t)
```
where `R` is an (optional) requirements annotation.
More generally, any argument `x1 ... xn` that is not marked with `:implicit` is assumed to be in the argument list of the declared rule.

### Example: Reflexivity of Equality as an Axiom

Note the following definition is equivalent to the previously declared version of `refl`:
```
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-axiom refl ((T Type :implicit) (t T))
    (= t t)
)
```
The argument `T` to `refl` has been marked as `:implicit`, and thus it does not appear in the argument list.

#  <a name="proofs"></a> Writing Proofs

The ALF language provies the commands `assume` and `step` for defining proofs. Their syntax is given by:
```
(assume <symbol> <term>)
(step <symbol> <term>? :rule <symbol> <premises>? <arguments>?)
where
<premises>      ::= :premises (<term>*)
<arguments>     ::= :args (<term>*)
```
### Example proof: symmetry of equality

```
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-rule symm ((T Type) (t T) (s T))
    :premises ((= t s))
    :conclusion (= s t)
)
(declare-sort Int 0)
(declare-const a Int)
(declare-const b Int)
(assume @p0 (= a b))
(step @p1 (= b a) :rule symm :premises (@p0))
```

## Proofs with local assumptions

The ALF language includes commands `assume-push` and `step-pop` with the same syntax as `assume` and `step` respectively.
However, the former can be seen as introducing a local assumption that is consumed by the latter.
We give an example of this in following.

```
(declare-const => (-> Bool Bool Bool))
(declare-rule implies-intro ((F Bool) (G Bool))
  :assumption F
  :premises (G)
  :conclusion (=> F G)
)
(declare-rule contra ((F Bool))
  :premises (false)
  :args (F)
  :conclusion F)
(assume-push @p1 false)
(step @p2 true :rule contra :premises (@p1) :args (true))
(step-pop @p3 (=> false true) :rule implies-intro :premises (@p2))
```

In this signature, we define a proof rule for implication introduction.
The rule takes an assumption `:assumption F`, which denotes that it will consume a local assumption introduced by `assume-push`.
We also define a rule for contradiction that states any formula can be proven if we prove `false`.

The command `assume-push` denotes that `@p1` is a (locally assumed) proof of `false`.
The proof `@p1` is then used as a premise to the step `@p2`, which proves `true`.
The command `step-pop` then consumes the proof of `@p1` and binds `@p3` to a proof of `(=> false true)`.
Notice that `@p1` is removed from scope after `@p3` is applied.

Locally assumptions can be arbitrarily nested, for example the above can be extended to:
```
...
(assume-push @p0 true)
(assume-push @p1 false)
(step @p2 true :rule contra :premises (@p1) :args (true))
(step-pop @p3 (=> false true) :rule implies-intro :premises (@p2))
(step-pop @p4 (=> true (=> false true)) :rule implies-intro :premises (@p3))
```

# Side Conditions

The ALF language supports a command for defining ordered lists of rewrite rules that can be seen as computational side conditions.
The syntax for this command is as follows.
```
(program <symbol> (<typed-param>*) (<type>*) <type> ((<term> <term>)+))
```
This command declares a program named `<symbol>`.
The provided type parameters are implicit and are used to define its type signature and body.

The type of the program is given immediately after the parameter list, provided as a list of argument types and a return type.
The semantics of the program is given by a non-empty list of pairs of terms, which we call its *body*.
For program `f`, This list is expected to be a list of terms of the form `(((f t11 ... t1n) r1) ... ((f tm1 ... tmn) rm))`
where `t11...t1n, ..., tm1...tmn` do not contain computational operators.
A (ground) term `(f s1 ... sn)` evaluates by finding the first term in the first position of a pair of this list that matches it for substitution `S`, and returns the result of applying `S` to the right hand side of that pair.
If no such term can be found, then the application does not evaluate.

> Terms in program bodies are not statically type checked. Evaluating a program may introduce non-well-typed terms if the program body is malformed.

> For each case `((f ti1 ... tin) ri)` in the program body, the free parameters in `ri` are required to be a subset of the free parameters in `(f ti1 ... tin)`. Otherwise, an error is thrown.

> If a case is provided `(si ri)` in the definition of program `f` where `si` is not an application of `f`, an error is thrown.
Furthermore, if `si` contains any computational operators (i.e. those with `alf.` prefix), then an error is thrown.

### Example: Finding a child in an `or` term

The following program (recursively) computes whether a formula `l` is contained as the direct child of an application of `or`:
```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(program contains
    ((l Bool) (x Bool) (xs Bool :list))
    (Bool Bool) Bool
    (
        ((contains false l)     false)
        ((contains (or l xs) l) true)
        ((contains (or x xs) l) (contains l xs))
    )
)
```

First, we declare the parameters `l, x, xs`, each of type `Bool`.
These parameters are used for defining the body of the program, but do *not* necessarily coincide with the expected arguments to the program.
We then declare the type of the program `(Bool Bool) Bool`, i.e. the type of `contains` is a function expecting two Booleans and returning a Boolean.
The body of the program is then given in three cases.
First, terms of the form `(contains false l)` evaluate to `false`, that is, we failed to find `l` in the second argument.
Second, terms of the form `(contains (or l xs) l)` evaluate to `true`, that is we found `l` in the first position of the second argument.
Otherwise, terms of the form `(contains (or x xs) l)` evaluate in one step to `(contains xs l)`, in other words, we make a recursive call to find `l` in the tail of the list `xs`.

In this example, since `xs` was marked with `:list`, the terms `(or l xs)` and `(or x xs)` are desugared to terms where `xs` is matched with the tail of the input.
The next two examples show variants where an incorrect definition of this program is defined.

> As mentioned in [list-computation](#list-computation), ALF has dedicated support for operators over lists.
For the definition of `contains` in the above example, the term `(contains l c)` is equivalent to `(alf.not (alf.is_neg (alf.find or c l)))`.
Computing the latter is significantly faster in practice in the ALF checker.

### Example: Finding a child in an `or` term (incorrect version)
```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(program contains
    ((l Bool) (x Bool) (xs Bool))
    (Bool Bool) Bool
    (
        ((contains false l)     false)
        ((contains (or l xs) l) true)
        ((contains (or x xs) l) (contains l xs))
    )
)
```

In this variant, `xs` was not marked with `:list`.
Thus, `(or l xs)` and `(or x xs)` are desugared to `(or l (or xs false))` and `(or x (or xs false))` respectively.
In other words, these terms will match `or` terms with *exactly* two children, for example `(contains (or a b) a)` will still evaluate to `true`.
However, `(contains (or a b c) a)` does not evaluate in this example.

### Example: Finding a child in an `or` term (incorrect version 2)
```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(program contains
    ((l Bool) (x Bool :list) (xs Bool :list))
    (Bool Bool) Bool
    (
        ((contains false l)     false)
        ((contains (or l xs) l) true)
        ((contains (or x xs) l) (contains l xs))
    )
)
```
In this variant, both `xs` and `x` were marked with `:list`.
The ALF checker will reject this definition since it implies that a computational operator appears in a pattern for matching.
In particular, the term `(or x xs)` is equivalent to `(alf.list_concat or x xs)` after desugaring.
Thus, the third case of the program, `(contains (alf.list_concat or x xs) l)`, is not a legal pattern.

### Example: Substitution

```
(program substitute
  ((T Type) (U Type) (S Type) (x S) (y S) (f (-> T U)) (a T) (z U))
  (S S U) U
  (
  ((substitute x y x)     y)
  ((substitute x y (f a)) (_ (substitute x y f) (substitute x y a)))
  ((substitute x y z)     z)
  )
)
```

The term `(substitute x y t)` replaces all occurrences of `x` by `y` in `t`.
Note that this side condition is fully general and does not depend on the shape of terms in `t`.
In detail, recall that the ALF checker treats all function applications as curried (unary) applications.
In particular, this implies that `(f a)` matches any application term, since both `f` and `a` are parameters.
Thus, the side condition is written in three cases: either `t` is `x` in which case we return `y`, `t` is a function application in which case we recurse, or otherwise `t` is a constant not equal to `x` and we return itself.

### Example: Term evaluator

```
(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const + (-> Int Int Int))
(declare-const - (-> Int Int Int))
(declare-const < (-> Int Int Bool))
(declare-const <= (-> Int Int Bool))

(program run_evaluate ((T Type) (U Type) (S Type) (a T) (b U) (z S))
    (S) S
    (
      ((run_evaluate (= a b))  (alf.is_eq (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (< a b))  (alf.is_neg (run_evaluate (- a b))))
      ((run_evaluate (<= a b)) (let ((x (run_evaluate (- a b))))
                                 (alf.or (alf.is_neg x) (alf.is_eq x 0))))
      ((run_evaluate (+ a b))  (alf.add (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (- a b))  (alf.add (run_evaluate a) (alf.neg (run_evaluate b))))
      ((run_evaluate z)        z)
    )
)
```
The above example recursively evaluates arithmetic terms and predicates according to their intended semantics.

### Example: A computational type rule

```
(declare-sort Int 0)
(declare-sort Real 0)
(program arith.typeunion ()
    (Type Type) Type
    (
      ((arith.typeunion Int Int) Int)
      ((arith.typeunion Int Real) Real)
      ((arith.typeunion Real Int) Real)
      ((arith.typeunion Real Real) Real)
    )
)
(declare-const + (-> (! Type :var T :implicit)
                     (! Type :var U :implicit)
                     T U (arith.typeunion T U)))
```

In the above example, a side condition is being used to define the type rule for the function `+`.
In particular, `arith.typeunion` is a program taking two types and returning a type, which is `Real` if either argument is `Real` or `Int` otherwise.
The return type of `+` invokes this side condition, which conceptually is implementing a policy for subtyping over arithmetic types.

### Example: Conversion to DIMACS

```
(declare-sort String 0)
(declare-consts <string> String)
(declare-const not (-> Bool Bool))
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)

(program to_drat_lit ((l Bool))
  (Bool) Int
  (
    ((to_drat_lit (not l))  (alf.neg (alf.hash l)))
    ((to_drat_lit l)        (alf.hash l))
  )
)
(program to_drat_clause ((l Bool) (C Bool :list))
  (Bool) String
  (
    ((to_drat_clause false)    "0")
    ((to_drat_clause (or l C)) (alf.concat (alf.to_str (to_drat_lit l)) " " (to_drat_clause C)))
    ((to_drat_clause l)        (alf.concat (alf.to_str (to_drat_lit l)) " 0"))
  )
)
(program to_dimacs ((C Bool) (F Bool :list))
  (Bool) String
  (
    ((to_dimacs true)       "")
    ((to_dimacs (and C F))  (alf.concat (to_drat_clause C) " " (to_dimacs F)))
  )
)
```
The above program `to_dimacs` converts an ALF formula into DIMACS form, where `alf.hash` is used to assign atoms to integer identifiers.

## Match statements in ALF

The ALF checker supports an operator `alf.match` for performing pattern matching on a target term. The syntax of this term is:
```
(alf.match (<typed-param>*) <term> ((<term> <term>)*))
```
The term `(alf.match (...) t ((s1 r1) ... (sn rn)))` finds the first term `si` in the list `s1 ... sn` that `t` can be matched with under some substitution and returns the result of applying that substitution to `ri`.

> Match terms require the free parameters of `ri` are a subset of the provided parameter list.
In other words, all patterns must only involve parameters that are locally bound as the first argument of the match term.
Also, similar to programs, the free parameters of `ri` that occur in the parameter list must be a subset of `si`, or else an error is thrown.

> Like programs, match terms are not statically type checked.

### Examples of legal and illegal match terms

```
(declare-sort Int 0)
(declare-const F Bool)
(declare-const a Int)
(declare-const P (-> Int Bool))
(declare-const f (-> Int Int))
; Legal match terms:
(define test1 ((x Int))
    (f (alf.match ((y Int)) x 
            (
                (a a) 
                (b b) 
                ((f (f a)) a)   ; can use arbitrary nesting in pattern terms
                ((f (f y)) b)
                (y a)           ; note that using a parameter as a pattern acts as a default case
            )
        )))
(define test2 ((F Bool) (y Int)) 
    (alf.match ((x Int)) F 
        (
            ((P x) y)           ; ok since y is bound at a higher scope and x is bound locally
        )
    ))

; Illegal match terms:
(define test3 ((F Bool) (y Int)) 
    (alf.match ((x Int)) F 
        (
            ((P y) a)       ; since y is not locally bound
        )
    ))
(define test4 ((F Bool) (y Int)) 
    (alf.match ((x Int)) F 
        (
            ((P a) x)       ; since x does not occur in (P a)
        )))  
```


### Example: Proof rule for symmetry of (dis)equality

```
(declare-sort Int 0)
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const not (-> Bool Bool))
(declare-rule symm ((F Bool))
    :premises (F)
    :conclusion
        (alf.match ((t1 Int) (t2 Int)) F
            (
                ((= t1 t2)       (= t2 t1))
                ((not (= t1 t2)) (not (= t2 t1)))
            )
        )
)
```
The above rule performs symmetry on equality or disequality.
It matches the given premise `F` with either `(= t1 t2)` or `(not (= t1 t2))` and flips the terms on the sides of the (dis)equality.

Internally, the semantics of `alf.match` can be seen as an (inlined) program applied to its head, such that the above example is equivalent to:
```
(declare-sort Int 0)
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const not (-> Bool Bool))
(program matchF ((t1 Int) (t2 Int))
    (Bool) Bool
    (
      ((matchF (= t1 t2))       (= t2 t1))
      ((matchF (not (= t1 t2))) (not (= t2 t1)))
    )
)
(declare-rule symm ((F Bool))
    :premises (F)
    :args ()
    :conclusion (matchF F)
)
```

> The ALF checker automatically performs the above transformation on match terms for consistency.
In more general cases, if the body of the match term contains free variables, these are added to the argument list of the internally generated program.

### Example: Proof rule for transitivity of equality with a premise list

```
(declare-sort Int 0)
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const and (-> Bool Bool Bool) :left-assoc)

(program mk_trans ((t1 Int) (t2 Int) (t3 Int) (t4 Int) (tail Bool :list))
    (Int Int Bool) Bool
    (
        ((mk_trans t1 t2 (and (= t3 t4) tail)) (alf.requires t2 t3 (mk_trans t1 t4 tail)))
        ((mk_trans t1 t2 true)                 (= t1 t2))
    )
)

(declare-rule trans (E Bool))
    :premise-list E and
    :conclusion
        (alf.match ((t1 Int) (t2 Int) (tail Bool :list)) E
        (
            ((and (= t1 t2) tail) (mk_trans t1 t2 tail))
        ))
)
```

For simplicity, the rule is given only for equalities of the integer sort, although this rule can be generalized.
The proof rule `trans` first packages an arbtirary number of premises, constructs a conjunction of these premises, which to bound to `E` and passed to the match term in the conclusion.
The recursive calls in the side condition `mk_trans` accumulate the endpoints of an equality chain and ensure via `alf.requires` that further equalities extend the left hand side of this chain.

# Including and referencing files

The ALF checker supports the following commands for file inclusion:
- `(include <string>)`, which includes the file indicated by the given string. The path to the file is taken relative to the directory of the file that includes it.
- `(reference <string> <symbol>?)`, which similar to `include` includes the file indicated by the given string, and furthermore marks that file as being the *reference input* for the current run of the checker (see below). The optional symbol can refer to a normalization routine (see below).

## Validation Proofs via Reference Inputs

When the ALF checker encounters a command of the form `(reference <string>)`, the checker enables a further set of checks that ensures that all assumptions in proofs correspond to assertions from the reference file.

In particular, when the command `(reference "file.smt2")` is read, the ALF checker will parse `file.smt2`.
The definitions and declaration commands in this file will be treated as normal, that is, they will populate the symbol table of the ALF checker as they normally would if they were to appear in an `*.smt3` input.
The commands of the form `(assert F)` will add `F` to a set of formulas we will refer to as the *reference assertions*.
Other commands in `file.smt2` (e.g. `set-logic`, `set-option`, and so on) will be ignored.

If alfc has read a reference file, then for each command of the form `(assume <symbol> G)`, alfc will check whether `G` occurs in the set of parsed reference assertions.
If it does not, then an error is thrown indicating that the proof is assuming a formula that is not a part of the original input.

> Only one reference command can be executed for each run of alfc.

> Incremental `*.smt2` inputs are not supported as reference files in the current version of alfc.

## Validation up to Normalization

Since the validation is relying on the fact that alfc can faithfully parse the original *.smt2 file, validation will only succeed if the signatures used by the ALF checker exactly match the syntax for terms in the *.smt2 file.
Minor changes in how terms are represented will lead to mismatches.
For this reason, alfc additionally supports providing an optional normalization routine via `(reference <string> <term>)`, which includes the file indicated by the given string and specifies all assumptions must match an assertion after running the provided normalization function.

For example:
```
(declare-sort Int 0)
(declare-sort Real 0)
(declare-const / (-> Int Int Real))
(program normalize ((T Type) (S Type) (f (-> S T)) (x S) (a Int) (b Int))
   (T) T
   (
     ((normalize (/ a b)) (alf.qdiv a b))
     ((normalize (f x))   (_ (normalize f) (normalize x)))
     ((normalize y)       y)
   )
)
(reference "file.smt2" normalize)
```
Here, `normalize` is introduced as a program which recursively replaces all occurrences of division (over integer constants) with the resulting rational constant.
This method can be used for handling solvers that interpret constant division as the construction of a rational constant.
The above program will be invoked on all formulas occuring in `assert` commands in `"file.smt2"` and subsequently formulas in `assume` commands.

# Oracles

The ALF checker supports a command, `declare-oracle-fun`, which associates the semantics of a function with an external binary.
We reference to such functions as *oracle functions*.
The syntax and semantics of such functions are described in [].

In particular, the ALF checker supports the command:
```
(declare-oracle-fun <symbol> (<type>*) <type> <symbol>)
```
Like `declare-fun`, this command declares a constant named `<symbol>` whose type is given by the argument types and return type.
In addition, a symbol is provided at the end of the command which specifies the name of executable command to run.
Ground applications of oracle functions are eagerly evaluated by invoking the binary and parsing its result, which we describe in more detail in the following.

### Example: Oracle isPrime

```
(declare-sort Int 0)
(declare-consts <numeral> Int)
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const >= (-> Int Int Bool))

(declare-oracle-fun runIsPrime (Int) Bool ./isPrime)

(declare-rule ((x Int) (y Int) (z Int))
    :premises ((>= z 2) (= (* x y) z))
    :requires (((runIsPrime z) false))
    :conclusion false)
```

In the above example, `./isPrime` is assumed to be an executable that given text as input returns either the text `true` denoting that the input text denotes a prime integer value or `false` if the text denotes a composite integer value.
Otherwise, it is expected to exit with a (non-zero) error code.

An application of `(runIsPrime z)` for a ground term `z` invokes `./isPrime`.
If `./isPrime` returns with an error, then `(runIsPrime z)` does not evaluate.
Otherwise, `(runIsPrime z)` evaluates to the result of parsing its output using the current ALF parser state.
In this example, an output of response of `true` (resp. `false`) from the executable will be parsed back at the Boolean value `true` (resp. `false`).
More generally, input and output of oracles may contain symbols that are defined in the current ALF parser state.
The user is responsible that the input can be properly parsed by the oracle, and the outputs of oracles can be properly parsed by the ALF checker.

In the above example, a proof rule is then defined that says that if `z` is an integer greater than or equal to `2`, is the product of two integers `x` and `y`, and is prime based on invoking `runIsPrime` in the given requirement, then we can conclude `false`.

# Appendix

## Command line options of alfc

The ALF command line interface can be invoked by `alfc <option>* <file>` where `<option>` is one of the following:
- `--binder-fresh`: binders generate fresh variables when parsed in proof files.
- `--help`: displays a help message.
- `--no-normalize-dec`: do not treat decimal literals as syntax sugar for rational literals.
- `--no-normalize-hex`: do not treat hexadecimal literals as syntax sugar for binary literals.
- `--no-parse-let`: do not treat `let` as a builtin symbol for specifying terms having shared subterms.
- `--no-print-let`: do not letify the output of terms in error messages and trace messages.
- `--no-rule-sym-table`: do not use a separate symbol table for proof rules and declared terms.
- `--show-config`: displays the build information for the given binary.
- `--stats`: enables detailed statistics.
- `--stats-compact`: print statistics in a compact format.
- `-t <tag>`: enables the given trace tag (for debugging).
- `-v`: verbose mode, enable all standard trace messages.

## Full syntax for ALF commands

Valid inputs to the ALF checker are `<alf-command>*`, where:

```
;;;
<alf-command> ::=
    (assume <symbol> <term>) |
    (assume-push <symbol> <term>) |
    (declare-axiom <symbol> (<typed-param>*) <reqs>? <term>) |
    (declare-consts <lit-category> <type>) |
    (declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*) |
    (declare-oracle-fun <symbol> (<type>*) <type> <symbol>) |
    (declare-rule <symbol> (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? :conclusion <term>) |
    (declare-type <symbol> (<type>*)) |
    (define <symbol> (<typed-param>*) <term>) |
    (define-type <symbol> (<type>*) <type>) |
    (include <string>) |
    (program <symbol> (<typed-param>*) (<type>*) <type> ((<term> <term>)+)) |
    (reference <string> <symbol>?) |
    (step <symbol> <term>? :rule <symbol> <simple-premises>? <arguments>?) |
    (step-pop <symbol> <term>? :rule <symbol> <simple-premises>? <arguments>?) |
    <common-command>

;;;
<common-command> ::=
    (declare-const <symbol> <type> <attr>*)
    (declare-datatype <symbol> <datatype-dec>) |
    (declare-datatypes (<sort-dec>^n) (<datatype-dec>^n)) |
    (declare-fun <symbol> (<type>*) <type> <attr>*) |
    (declare-sort <symbol> <numeral>) |
    (define-const <symbol> <term>) |
    (define-fun <symbol> (<typed-param>*) <type> <term>) |
    (define-sort <symbol> (<symbol>*) <type>) |
    (echo <string>?) |
    (exit) |
    (reset)

;;;
<smtlib2-command> ::=
    (assert <term>) |
    (check-sat) |
    (check-sat-assuming (<term>*)) |
    (set-info <attr>) |
    (set-logic <symbol>) |
    (set-option <attr>) |
    <common-command>

;;;
<keyword>       ::= :<symbol>
<attr>          ::= <keyword> <term>?
<term>          ::= <symbol> | (<symbol> <term>+) | (! <term> <attr>+) | (alf.match (<typed-param>*) <term> ((<term> <term>)*))
<type>          ::= <term>
<typed-param>   ::= (<symbol> <type> <attr>*)
<sort-dec>      ::= (<symbol> <numeral>)
<sel-dec>       ::= (<symbol> <type>)
<cons-dec>      ::= (<symbol> <sel-dec>*)
<datatype-dec>  ::= (<cons-dec>+)
<lit-category>  ::= '<numeral>' | '<decimal>' | '<rational>' | '<binary>' | '<hexadecimal>' | '<string>'

;;;
<assumption>      ::= :assumption <term>
<premises>        ::= <simple-premises> | :premise-list <term> <term>
<simple-premises> ::= :premises (<term>*)
<arguments>       ::= :args (<term>*)
<reqs>            ::= :requires ((<term> <term>)*)

```

Moreover, a valid input for a file included by the ALF command `<reference>` is `<smtlib2-command>*`;
a valid input for a file included by the ALF command `<include>` is `<alf-command>*`.

### <a name="bv-literals"></a>Definitions of Non-Core Evaluation Operators

The following signature can be used to define operators that are not required to be supported as core evaluation operators.

```

; Returns true if x is a numeral literal.
(define alf.is_z ((T Type :implicit) (x T))
  (alf.is_eq (alf.to_z x) x))

; Returns true if x is a rational literal.
(define alf.is_q ((T Type :implicit) (x T))
  (alf.is_eq (alf.to_q x) x))

; Returns true if x is a binary literal.
(define alf.is_bin ((T Type :implicit) (x T))
  (alf.is_eq (alf.to_bin (alf.len x) x) x))

; Returns true if x is a string literal.
(define alf.is_str ((T Type :implicit) (x T))
  (alf.is_eq (alf.to_str x) x))

; Returns true if x is a Boolean literal.
(define alf.is_bool ((T Type :implicit) (x T))
  (alf.ite (alf.is_eq x true) true (alf.is_eq x false)))

; Returns true if x is a variable.
(define alf.is_var ((T Type :implicit) (x T))
  (alf.is_eq (alf.var (alf.nameof x) (alf.typeof x)) x))

; Compare arithmetic greater than. Assumes x and y are values.
; Returns true if x > y.
(define alf.gt ((T Type :implicit) (x T) (y T))
  (alf.is_neg (alf.add (alf.neg x) y)))

; An arbitrary deterministic comparison of terms. Returns true if a > b based
; on this ordering.
(define alf.com ((T Type :implicit) (U Type :implicit) (a T) (b U))
  (alf.is_neg (alf.add (alf.hash b) (alf.neg (alf.hash a)))))

```

## Proofs as terms

This section overviews the semantics of proofs in the ALF language.
Proof checking can be seen as a special instance of type checking terms involving the `Proof` and `Quote` types.
The type system of the ALF can be summarized as follows, where `t : S` are assumed axioms for all atomic terms `t` of type `S`:

```
f : (-> (Quote u) S)  t : T
---------------------------- if u * sigma = t
(f t) : S * sigma


f : (-> U S)  t : T
------------------- if U * sigma = T
(f t) : S * sigma

for all other (non-Quote) types U.

```

The command:
```
(declare-rule s ((v1 T1) ... (vi Ti)) 
    :premises (p1 ... pn) 
    :args (t1 ... tm) 
    :requires ((r1 s1) ... (rk sk)) 
    :conclusion t)
```
can be seen as syntax sugar for:
```
(declare-fun s
    (-> (! T1 :var v1 :implicit) ... (! Ti :var vi :implicit)
        (Proof p1) ... (Proof pn)
        (Quote t1) ... (Quote tm)
        (alf.requires r1 s1 ... (alf.requires rk sk
            (Proof t)))))
```

The command:
```
(assume s f)
```
can be seen as syntax sugar for:
```
(declare-const s (Proof f))
```

The command:
```
(step s f :rule r :premises (p1 ... pn) :args (t1 ... tm))
```
can be seen as syntax sugar for:
```
(define-fun s () (Proof f) (r p1 ... pn t1 ... tm))
```
Notice this is only the case if the declaration of `r` does not involve `:assumption` or `:premise-list`.
