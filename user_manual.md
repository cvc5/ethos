# The Ethos user manual

This is the user manual for Ethos, an efficient and extensible tool for checking proofs of Satisfiability Modulo Theories (SMT) solvers.

## Building the Ethos executable

The source code for Ethos is available at <https://github.com/cvc5/ethos>.
To build ethos, run:

```shell
mkdir build
cd build
cmake ..
make
```

The `ethos` binary will be available in `build/src/`.

### Debug build

By default, the above will be a production build of `ethos`. To build a debug version of `ethos`, that is significantly slower but has assertions and trace messages enabled, run:

```shell
mkdir build
cd build
cmake -DCMAKE_BUILD_TYPE=Debug ..
make
```

The `ethos` binary will be available in `build/src/`.

## Command line interface

Ethos can be run from the command line via:

```shell
ethos <option>* <file>
```

The set of available options `<option>` are given in the appendix. Note the command line interface of `ethos` expects exactly one file (which itself may reference other files via the `include` command as we will see later). The file and options can appear in any order.

The `<file>` passed to Ethos on the command line is either:

- A Eunoia file, defining a background theory or proof calculus (extension `.eo`), or
- A file containing a proof.

Any file with extension that is not `.eo` is assumed to be the latter.
All proof files are expected to contain a reference to a Eunoia file that defines its symbols via an include command or using the command line option `--include=X`.
Complete details on the categories of files accepted by Ethos are described later in this document [here](#full-syntax).

When invoking Ethos on the command line, Ethos will either emit an error message indicating:

- the kind of failure (type checking, proof checking, lexer error)
- the line and column of the failure

or will print a [successful response](#responses) when it finished parsing all commands in the file or encounters and `exit` command.
Further output can be given by user-provided `echo` commands.

### Streaming input to Ethos

The `ethos` binary accepts input piped from stdin. The following are all equivalent ways of running `ethos`:

```shell
% ethos <file>
% ethos < <file>
% cat <file> | ethos
```

## Overview of Eunoia's features

Eunoia is the name of the logical framework and language that is supported natively by the Ethos checker.
Although it is a general logical framework, Eunoia is geared towards defining proof systems used by SMT solvers and writing proofs in those systems.

Eunoia files are text files that are typically given the suffix `*.eo`.

The core features of Eunoia include:

- A syntax and type system for defining theory signatures that follows those of SMT-LIB version 3.0.
- Constructs for associating syntactic categories (as specified by SMT-LIB e.g. `<numeral>`) with types.
- A command, `declare-rule`, for defining proof rules.
- A set of commands for specifying proofs (`step`, `assume`, and so on), whose syntax closely follows that of the Alethe proof format (for details, see [here](https://verit.gitlabpages.uliege.be/alethe/specification.pdf)).
- A set of built-in basic types and a library of operations (`eo::add`, `eo::mul`, `eo::concat`, `eo::extract`) for performing computations over values.
  <!--CT It would be more consistent with the rest of the terminology to use `define-program` instead -->
- A command, `program`, for defining side conditions as an ordered list of rewrite rules.
- Commands for file inclusion (`include`) and referencing (`reference`). The latter command can be used to specify the name of an `*.smt2` input file that the proof is associated with.

In the following sections, we describe these features in more detail. A full syntax for the commands is given at the end of this document.

### Declaring theory signatures

In Eunoia, as in SMT-LIB version 3.0, a common BNF is used to specify _terms_ (expressions denoting values), _types_ (expressions denoting sets of values) and _kinds_ (expressions denoting sets of types).
In this document, unless specified otherwise, we will use _term_ more generally to refer to a value term, a type, or a kind.
Terms are composed of applications, built-in operators of the language (e.g., for performing computations, see [computation](#computation)), literals (see [literals](#literals)), and three kinds of atomic terms (_constants_, _variables_, and _parameters_) which we describe below.
A _function (symbol)_ is an atomic term having a function type, that is, a type of the form `(-> ... ...)`.
The builtin `eo::define` binder can be used for specifying terms that contain common subterms analogously to `let` binders in other languages.

The core language of Eunoia does not have any builtin SMT-LIB theories.
Instead, SMT-LIB theories may defined as Eunoia signatures.
For this purpose, the Eunoia language has the following builtin constants:

- `Type`, denoting the kind of all types,
- `->`, denoting the function type,
- `_`, denoting (higher-order) function application,
- `Bool`, denoting the Boolean type,
- `true` and `false`, denoting the two values of type `Bool`.

> __Note:__ The core logic of Ethos also uses several builtin types (e.g. `Proof` and `Quote`) which define the semantics of proof rules. These types are intentionally to exposed to the user. Details on then can be found throughout this document. More details on the core logic of Ethos will be available in a forthcoming publication.

In the following, we informally use the syntactic categories `<symbol>` to denote an SMT-LIB 3.0 symbol, `<term>` to denote an SMT-LIB term and `<type>` to denote a term whose type is `Type`. The syntactic category `<typed-param>` is defined, BNF-style, as `(<symbol> <type> <attr>*)`. It binds `<symbol>` as a fresh parameter of the given type and attributes (if provided).

The following commands are supported for declaring and defining types and terms. The first set of commands are identical to those in SMT-LIB version 3.0:

- `(declare-const <symbol> <type> <attr>*)` declares a constant named `<symbol>` whose type is `<type>`. Can be given an optional list of attributes (see [attributes](#attributes)).
<!-- Moved here because it is present in SMT-LIB 3 -->

- `(declare-consts <lit-category> <type>)` declares the class of symbols denoted by the literal category to have the given type.

- `(declare-datatype <symbol> <datatype-dec>)` defines a datatype `<symbol>`, along with its associated constructors, selectors, discriminators and updaters.

- `(declare-datatypes (<sort-dec>^n) (<datatype-dec>^n))` defines a list of `n` datatypes for some `n>0`.

- `(exit)` causes the checker to immediately terminate.

- `(reset)` removes all declarations and definitions and resets the global scope. This command is similar in nature to its counterpart in SMT-LIB.

The Eunoia language contains further commands for declaring symbols that are not standard SMT-LIB version 3.0:

- `(define <symbol> (<typed-param>*) <term> <attr>*)`, defines `<symbol>` to be a lambda term whose arguments and body are given by the command, or just an arbitrary term defined by the provided the body, if the argument list is empty (i.e., it may be a non-function term). Note that in contrast to the SMT-LIB command `define-fun`, a return type is not provided. It is also possible to provide attributes to the definition: e.g. `:type`, which instructs the checker to perform type checking on the given term (see [type checking define](#tcdefine)).

- `(declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*)` declares a globally scoped variable named `<symbol>` whose expected arguments are given by the argument list, and whose return type is `<type>`.

> __Note:__ Variables are internally treated the same as constants by Ethos. However, they are provided as a separate category, e.g., for user signatures that wish to distinguish universally quantified variables from free constants. They also have a relationship with user-defined binders, see [binders](#binders), and can be accessed via the builtin operator `eo::var` (see [computation](#computation)).

> __Note:__ Symbol overloading is supported, see [overloading](#overloading).

#### Example: Basic Declarations

```smt
(declare-const Int Type)
(declare-const c Int)
(declare-const f (-> Int Int Int))
(declare-const g (-> Int (-> Int Int)))
(declare-const P (-> Int Bool))
```

Since Ethos does not assume any builtin definitions of SMT-LIB theories, definitions of standard symbols in SMT-LIB theories (such as `Int`, `+`, etc.) must be provided in Eunoia signatures. In the above example, symbol `c` is declared to be a constant (0-ary) symbol of type `Int`. The symbol `f` is a function taking two integers and returning an integer.

Observe that despite the use of different syntax in their declarations, the types of `f` and `g` in the above example are identical as `->` is a right-associative binary type constructor.

> __Note:__ In Eunoia, all functions are unary. In the above example, `(-> Int Int Int)` is internally treated as `(-> Int (-> Int Int))`. Correspondingly, applications of functions are curried, e.g. `(f a b)` is treated as `((f a) b)`, which in turn can be seen as `(_ (_ f a) b)` where `_` denotes higher-order function application.

#### Example: Basic Definitions

```smt
(declare-const not (-> Bool Bool))
(define id ((x Bool)) x)
(define notId ((x Bool)) (not (id x)))
```

In the example above, `not` is declared to be a unary function over Booleans. Two defined functions are given, the first being an identity function over Booleans, and the second returning the negation of the first.

Since `define` commands are treated as (hygienic) macro definitions, in this example, `id` is mapped to the lambda term whose SMT-LIB version 3 syntax is `(lambda ((x Bool)) x)`.
Furthermore, `notId` is mapped to the lambda term `(lambda ((x Bool)) (not x))`.
In other words, the following sequence of commands is equivalent to the one above after parsing:

```smt
(declare-const not (-> Bool Bool))
(define id ((x Bool)) x)
(define notId ((x Bool)) (not x))
```

#### Example: Polymorphic types

Eunoia supports the declaration of polymorphic types, that is, types depending on other types.

```smt
(declare-const Int Type)
(declare-const Array (-> Type Type Type))
(declare-const a (Array Int Bool))

(define IntArray ((T Type)) (Array Int T))
(declare-const b (IntArray Bool))
```

In the above example, we declare an integer type constructor of kind `Type` and array type constructor of kind `(-> Type Type Type)`.
We then declare two arrays, `a` and `b`, which, after parsing have an identical type, `(Array Int Bool)`.

<a name="tcdefine"></a>

### The :type attribute for definitions

To type check terms, `define` statements can be annotated with `:type <term>`.
This allows the user to eagerly check that a term has a particular type at the place where it is defined.
In particular:

```smt
(declare-const not (-> Bool Bool))
(define notTrue () (not true) :type Bool)
```

This indicates the checker to compare the type it computed for the term `(not true)`, with the specified type `Bool`. An error will be thrown if the two types are not identical.

### Declaring Parameterized Constants

The Eunoia language uses the command `declare-parameterized-const`, for declaring constants that have (possibly) dependent types.
In particular, this command allows naming arguments of functions and specifying that they are implicit.
The syntax of this command is the following:

```smt
(declare-parameterized-const <symbol> (<typed-param>*) <type> > <attr>*)
```

Consider the following example:

```smt
(declare-const Int Type)
(declare-parameterized-const eq ((T Type)) (-> T T Bool))
(define P ((x Int) (y Int)) (eq Int x y))
```

The above example declares a predicate symbol `eq` whose first argument is a type, that is given name `T`. It then expects two terms of type `T` and returns a `Bool`. In the definition of `P`, `eq` is applied to two variables, with type `Int` explicitly provided.

In contrast, the example below declares a predicate `=` where the type of the arguments is implicit (this corresponds to the SMT-LIB standard definition of `=`). An implicit argument for a parameterized constant can be given by the annotation `:implicit`. In the definition of `P`, the type `Int` of the arguments is not provided.

```smt
(declare-const Int Type)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(define P ((x Int) (y Int)) (= x y))
```

In general, an argument can be made implicit if its value can be inferred from the type of later arguments.

We call `T` in the above definitions a _parameter_.
Typically, the free parameters of the return type of a function should be contained in an explicit argument.
If not, the function is considered *ambiguous* and requires an annotation with the SMT-LIB syntax `as`.
For details, see [ambiguous functions](#amb-functions).

> __Note:__ Internally, parameters `(t T)` in the command `declare-parameterized-const` are handled specially in the type system. In particular `(declare-parameterized-const foo ((T Type)) T)` defines `foo` to be of "quote arrow" type, `(~> T T)`, where the argument to `foo` is bound to `T`, e.g. `(foo Int)` binds `T` to `Int` and thus has type `Int`. Technical details of the type system can be found at the end of this manual.

> __Note:__ Internally, `(t T :implicit)` drops `t` from the list of arguments of the function type we are defining.

<a name="opaque"></a>

### The :opaque annotation

The attribute `:opaque` can be used to denote that a distinguished argument to a function.
In particular, functions with opaque arguments intuitively can be considered a _family_ of functions indexed by their opaque arguments.
An example of this annotation is the following:

```smt
(declare-const Array (-> Type Type Type))
(declare-parameterized-const @array_diff
  ((T Type :implicit) (U Type :implicit) (t (Array T U) :opaque) (u (Array T U) :opaque))
   T)

(declare-const Int Type)
(declare-const A (Array Int Int))
(declare-const B (Array Int Int))
(define d () (@array_diff A B) :type Int)
```

The above example declares a function `@array_diff` symbol.
This has two implicit type arguments `T` and `U` followed by two opaque array arguments and has `T` as a return type.
In the remainder of the example, we define `d` to be this function applied to the arrays `A` and `B`, where `d` has type `Int`.

Intuitively, `d` should be considered an atomic constant symbol, where `A` and `B` are its indices and not its children.
In particular, this means that any computation that pattern matches `d` will not consider it to be a function application.
We give examples of this later in [ex-substitution](#ex-substitution).

Functions can have both opaque and ordinary arguments, where the opaque arguments are expected to come first.
Return types can never be marked `:opaque` or a type error will be immediately reported.
The concatenation of the expected arguments can be passed to the symbol in the order they are given.
For example:

```smt
(declare-const Int Type)
(declare-parameterized-const @purify_fun ((f (-> Int Int) :opaque)) (-> Int Int))

(declare-const f (-> Int Int))
(declare-const a Int)
(define d () (@purify_fun f a) :type Int)
```

In this example, `@purify_fun` is declared as a function with one opaque argument, an ordinary integer argument, and returns an integer.
Intuitively, this definition is introducing a new function, indexed by a function, that is of type `(-> Int Int)`.
After parsing, the term `(@purify_fun f a)` is a function application whose operator is `(@purify_fun f)` and has a single child `a`.

> __Note:__ Opaque arguments should always be expected before other arguments. Otherwise all applications of the given function will be ill-typed.

<a name="attributes"></a>

### Declarations with attributes

The Eunoia language supports term annotations on declared constants which, for instance, allow the user to treat a constant as being variadic, i.e. taking an arbitrary number of arguments. The available annotations for this purpose are:

- `:right-assoc` (resp. `:left-assoc`) denoting that application of the declared binary constant to more than two terms are to be treated as right (resp. left) associative,

- `:right-assoc-nil <term>` (resp. `:left-assoc-nil <term>`) denoting that applications of the declared binary constant to one or more terms are to be treated as right (resp. left) associative, with the given `<term>` used as an additional rightmost (resp. leftmost) argument.

- `:chainable <symbol>` denoting that the arguments of the declared binary constant are chainable using the (binary) operator given by `<symbol>`,

- `:pairwise <symbol>` denoting that the arguments of the declared constant are treated pairwise using the (binary) operator given by `<symbol>`.

- `:arg-list <symbol>` denoting that the arguments of the declared constant are provided to the n-ary operator given by `<symbol>`. The annotated symbol is is unary, taking the result of that operator.

- `:binder <symbol>` denoting that the first argument of the declared constant can be provided using a syntax for variable lists whose constructor is the one provided by `<symbol>`.

A declared function can be marked with at most one of the above attributes or an error is thrown.
We refer to constants with one of the above attributes (with the exception of `:binder`) as _variadic_ constants.
We describe these policies in detail in the following sections, which will describe how the parser desugars input syntax of the form `(f t1 ... tn)`.

Furthermore, a parameter may be marked with the following attribute:

- `:list`, denoting that the parameter should be treated as a list when appearing as a child of an application of a right (left) associative operator.


#### Right/Left associative

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc)
(define P ((x Bool) (y Bool) (z Bool)) (or x y z))
(define Q ((x Bool) (y Bool)) (or x y))
(define R ((x Bool)) (or x))
```

In the above example, `(or x y z)` is treated as `(or x (or y z))`.
The term `(or x y)` is not impacted by the annotation `:right-assoc` since it has fewer than 3 children.
The term `(or x)` is also not impacted by the annotation, and denotes the _partial application_ of `or` to `x`, whose type is `(-> Bool Bool)`.

Left associative can be defined analogously:

```smt
(declare-const and (-> Bool Bool Bool) :left-assoc)
(define P ((x Bool) (y Bool) (z Bool)) (and x y z))
```

In the above example, `(and x y z)` is treated as `(and (and x y) z)`.

Note that the type for right and left associative operators is typically `(-> T T T)` for some type `T`.
More generally, a constant declared with the `:right-assoc` annotation must have a type of the form `(-> T1 T2 T2)` for some types `T1` and `T2`. Similarly, a constant declared with the `:left-assoc` annotation must have a type of the form `(-> T1 T2 T1)`.

<a name="assoc-nil"></a>

#### Right/Left associative with nil terminator

Eunoia supports a variant of the aforementioned functionality where a (ground) nil terminator is provided.

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(define P ((x Bool) (y Bool) (z Bool)) (or x y z))
(define Q ((x Bool) (y Bool)) (or x y))
(define R ((x Bool) (y Bool)) (or x))
```

In the above example, `(or x y z)` is treated as `(or x (or y (or z false)))`,
`(or x y)` is treated as `(or x (or y false))`,
and `(or x)` is treated as `(or x false)`.
In contrast, if `or` was annotated with `left-associative-nil`,
`(or x y z)` would be treated as `(or (or (or false x) y) z)`,
`(or x y)` as `(or (or false x) y)`,
and `(or x)` as `(or false x)`.

The advantage of right or left associative operators with nil terminators is that the terms they specify are unambiguous, which is not the case for right or left associative operators without nil terminators.
Consider the following example:

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(define P1 ((x Bool) (y Bool) (z Bool)) (or x (or y z)))
(define P2 ((x Bool) (y Bool) (z Bool)) (or x y z))
```

If `or` had been marked `:right-assoc`, after desugaring, the abstract syntax tree for (the terms named) `P2` would have been the same `P1`.
In contrast, marking `or` with `:right-assoc-nil false` leads after desugaring to the distinct terms

- `(or x (or (or y (or z false)) false))` for `P1` and
- `(or x (or y (or z false)))` for `P2`.

> __Note:__ While the value provided for the `:right-assoc-nil` attribute (`false` in the example above) can be an arbitrary term of the proper type, it is advisable for it to be a _neutral_, or identity, element of the binary operator in question (`or` in the example). Otherwise, this gives rise to non-intuitive syntax.
>
> For instance, with
>
> ```smt
> (declare-const + (-> Int Int Int) :right-assoc-nil 1)
> ```
>
> where `+` is meant to be the integer addition operator, the choice of `1` as terminator instead of the identity element `0` means that the expressions `(+ x (+ y z)))` and `(+ x y z)` desugar to terms (`(+ x (+ (+ y (+ z 1) 1)))` and `(+ x (+ y (+ z 1)))`, respectively) that are distinct not just syntactically but also semantically.

Right and left associative operators with nil terminators also have a relationship with list terms (as we will see in the following section), and in computational operators.

The type for right and left associative operators with nil terminators is typically `(-> T T T)` for some `T`, where their nil terminator has type `T`. More generally, a constant declared with the `:right-assoc-nil` annotation must have a type of the form `(-> T1 T2 T2)` where `T2` is the type of the nil constant, for some types `T1` and `T2`. Similarly, a constant declared with the `:left-associative` annotation must have a type of the form `(-> T1 T2 T1)` where `T1` is the type of the nil constant.

The nil terminator of a right associative operator may involve previously declared symbols in the signature.
For example:

```smt
(declare-const RegLan Type)
(declare-const re.all RegLan)
(declare-const re.inter (-> RegLan RegLan RegLan) :right-assoc-nil re.all)
```

This example defines the constant `re.all` (in SMT-LIB, this is the regular expression generating the set of all strings)
and the function `re.inter` (in SMT-LIB, the intersection of regular expressions), where the latter is defined to have a nil terminator
that references the free constant `re.all`.

However, when using `declare-const`, the nil terminator of an associative operator cannot depend on the parameters of the type of that function.
For example, say we wish to declare bitvector or (`bvor` in SMT-LIB), where its nil terminator is the bitvector zero.
The command `declare-parameterized-const` can be used to define a version of `bvor` whose nil terminator depends on `m`,
which we will describe later in [param-constants](#param-constants).

#### List

Parameters can be marked with the annotation `:list`.
This includes those in function symbol declarations, as well as parameters to (e.g. `define`, `program`, `declare-rule`) commands.
This annotation marks that the term should be treated as a list of arguments when it occurs as an argument of a right (left) associative operator with a nil element. Note the following example:

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(define P ((x Bool) (y Bool)) (or x y))
(define Q ((x Bool) (y Bool :list)) (or x y))
(declare-const a Bool)
(declare-const b Bool)
(define Paab () (P a (or a b)))
(define Qaab () (Q a (or a b)))
```

In the above example, note that `or` has been marked `:right-assoc-nil false`.
As before, the definition of `P` is syntax sugar for `(or x (or y false))`.
In contrast, the definition of `Q` is simply `(or x y)`, since `y` has been marked with `:list`.
Conceptually, our definition of `P` treats `y` as the second child of an `or` term, whereas our definition of `Q` treats `y` as the _tail_ of an `or` term.

Then, `P` and `Q` are both applied to the pair of arguments `a` and `(or a b)`.
In the former (i.e. `Paab`), the definition is equivalent after desugaring to `(or a (or (or a (or b false)) false))`, whereas in the latter (i.e. `Qaab`) the definition is equivalent after desugaring to `(or a (or a (or b false)))`.
In other words, the definitions of `Paab` and `Qaab` are equivalent to the terms `(or a (or a b))` and `(or a a b)` respectively prior to desugaring.

More generally, for an right-associative operator `f` with nil terminator `nil`,
the term `(f t1 ... tn)` is de-sugared based on whether each `t1 ... tn` is marked with `:list`.

- The nil terminator is inserted at the tail of the function application unless `tn` is marked as `:list`,
- If `ti` is marked as `:list` where `1<=i<n`, then `ti` is prepended to the overall application using a concatentation operation `eo::list_concat`. The semantics of this operator is provided later in [list-computation](#list-computation).

In detail, the returned term from desugaring `(f t1 ... tn)` is constructed inductively.
If `tn` is marked with `:list`, the returned term is initialized to `tn` and we process children `ti` from `i = n-1 ... 1`.
If `tn` is not marked with `:list`, the return term is initialized to the nil terminator of `f` and we process children `ti` from `i = n .. 1`.
For each term `ti` we process, the returned term `r` is updated to `(f ti r)` if `ti` is not marked with `:list`, or to `(eo::list_concat f ti r)`
if `ti` is marked with `:list`.
Examples of this desugaring are given below.

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(define test ((x Bool) (y Bool) (z Bool :list) (w Bool :list))
    (and
        (or x y)        ; (or x (or y false))
        (or x z)        ; (or x z)
        (or x z y)      ; (or x (eo::list_concat or z (or y false)))
        (or x)          ; (or x false)
        (or z)          ; z
        (or z y w x)    ; (eo::list_concat or z (or y (eo::list_concat or w (or x false)))
    ))
```

Note that in the case of `(or z)`, no application of `or` is constructed, since only one argument term is given, since it is marked with `:list`.
In contrast, `(or x)` denotes the `or` whose children are `x` and `false`.

#### Right/Left associative with nil terminator, without singleton list

A further variant of right and left associative operators
avoids constructing lists with a single element.
In particular, note the following example:

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-non-singleton-nil false)
(define or_3 ((x Bool :list) (y Bool) (z Bool :list)) (or x y z))
(define Q () (or_3 (or a b) a false))
(define P () (or_3 false a false))
```

In this example, `or` has been marked `:right-assoc-non-singleton-nil false`.
This attribute is identical to `:right-assoc-nil false`, but where `or` applied to
a single child is instead replaced by the child itself.

We define a predicate `or_3` which concatenates three terms, the first
and third being lists and the middle child `y` being a Boolean.
The definition of `Q` is equivalent after desugaring to `(or a (or b (or a false)))`, which is identical to if `or` had been marked `:right-assoc-nil`.
The definition of `P` is equivalent after desugaring to `a`, which is not the same as `(or a false)`,
which would have been the result if `or` had been marked `:right-assoc-nil`.

More generally,
applications of `right-assoc-non-singleton-nil` operators `(f t1 ... tn)`
are desugared as follows.
First, we compute the result `t` of
desugaring `(f t1 ... tn)` using the policy described in the previous section,
where `f` is `right-assoc-nil`.
If at least two of `t1 ... tn` are not marked `:list`, we return `t`.
Otherwise we return the term `(eo::list_singleton_elim f t)`.
The semantics of `eo::list_singleton_elim` is provided later in [list-computation](#list-computation).
This means that the definition of `or_3` is desugared to
`(eo::list_singleton_elim or (eo::list_concat or x (or y z)))`
in the example above.

#### Chainable

```smt
(declare-const Int Type)
(declare-const and (-> Bool Bool Bool) :right-assoc)
(declare-const >= (-> Int Int Bool) :chainable and)
(define P ((x Int) (y Int) (z Int)) (>= x y z))
(define Q ((x Int) (y Int)) (>= x y))
```

In the above example, `(>= x y z w)` is syntax sugar for `(and (>= x y) (>= y z))`,
whereas the term `(>= x y)` is not impacted by the annotation `:chainable` since it has fewer than 3 children.

Note that the type for chainable operators is typically `(-> T T S)` for some types `T` and `S`,
where the type of its combining operator is `(-> S S S)`, and that operator has been marked as variadic via some attribute (e.g. `:right-assoc`).

A chainable operator applied to a single argument reduces to the neutral element of the combining operator.
For example, `(>= x)` is equivalent to `true`.

#### Pairwise

```smt
(declare-const Int Type)
(declare-const and (-> Bool Bool Bool) :right-assoc)
(declare-parameterized-const distinct ((T Type :implicit)) (-> T T Bool) :pairwise and)
(define P ((x Int) (y Int) (z Int)) (distinct x y z))
```

In the above example, `(distinct x y z)` is treated as `(and (distinct x y) (distinct x z) (distinct y z))`.

Note that the type for pairwise operators is typically `(-> T T S)` for some types `T` and `S`,
where the type of its combining operator is `(-> S S S)`,
and that operator has been marked as variadic via some attribute.

Similar to chainable operators,
a pairwise operator applied to a single argument reduces to the neutral element of the combining operator.
For example, `(distinct x)` is equivalent to `true`.

<a name="binders"></a>

#### Argument List

In practice, note that handling pairwise operators introduces quadratically many new terms.
As an alternative, an n-ary operator like `distinct` can be marked as taking an argument list,
as demonstrated in the example below.

```smt
(declare-const Int Type)
(declare-const @List Type)
(declare-const @nil @List)
(declare-parameterized-const @cons ((T Type :implicit)) (-> T @List @List)
 :right-assoc-nil @nil)
(declare-parameterized-const distinct ((xs @List)) Bool :arg-list @cons)
(define P ((x Int) (y Int) (z Int)) (distinct x y z))
```

In the above example, `(distinct x y z)` is desugared to `(distinct (@cons a b c))`,
which is further desugared to `(distinct (@cons a (@cons b (@cons c @nil))))`.
In contrast to the above example, the size of this term is not quadratic in size with respect to the input arguments.

This desugaring further takes into account if arguments to the annotated symbol have been marked with the attribute`:list`.
In particular, if there is only a single argument to `distinct`, and it is marked `:list`, then
it is *not* passed to the given list constructor but instead taken as the lone
argument. Note the following examples:

```
(define distinct-of ((xs @List :list))
  (distinct xs))
(define distinct-of2 ((T Type :implicit) (x T) (xs @List :list))
  (distinct x xs))
```

In the first definition, the argument to `distinct` is marked `:list`, hence
`(distinct xs)` is *not* desugared to `(distinct (@cons xs))`
since `xs` is marked `:list`.
In the second definition, `(distinct x xs)` has multiple arguments, hence
it is desugared to `(distinct (@cons x xs))`. This term is
not desugared further since `xs` is marked `:list`.

#### Binder

```smt
(declare-const Int Type)
(declare-const @List Type)
(declare-const @nil @List)
(declare-parameterized-const @cons ((T Type :implicit)) (-> T @List @List)
 :right-assoc-nil @nil)
(declare-const forall (-> @List Bool Bool) :binder @cons)
(declare-const P (-> Int Bool))

(define Q1 () (forall ((x Int)) (P x)))
(define Q2 () (forall ((x Int)) (P x)))
(define Q3 () (forall ((y Int)) (P y)))

(define x () (eo::var "x" Int))
(define Q4 () (forall (@cons x) (P x)))
```

In the above example, `forall` is declared as a binder.
This indicates that the parser (optionally) accepts a variable list as the first argument when parsing applications of `forall` instead of a term.
In particular, in the last two commands, the parser accepts `(forall ((x Int)) (P x))` for the variable list containing `x`.
A variable list parsed in this way binds the symbol `x` to a variable of type `Int` when parsing the remaining arguments of `forall`, i.e. its body.
The variable list passed as the first argument to the binder is determined by applying the specified constructor (in this case `@cons`) to the list of variables, so that `(forall ((x Int)) (P x))` is syntax sugar for `(forall (@cons x) (P x))`.
The constructor specified in declarations of binders should accept a variable number of arguments, e.g. `@cons` is declared with attribute `:right-assoc-nil`.

Variables introduced when parsing binders are always the same for each (symbol, type) pair.
In particular, this means that the definitions of `Q1` and `Q2` are syntactically identical in the above example.
On the other hand, the definition `Q3` is distinct from both of these, since `y` is a distinct variable from `x`.

Furthermore, note that a binder also may accept an explicit term as its first argument.
In the above example, `Q4` has `(@cons x)` as its first argument, where `x` was explicitly defined as a variable.
This means that the definition of `Q4` is also syntactically equivalent to the definition of `Q1` and `Q2`.

#### Further notes on constants with attributes

We have described ways Ethos parses (or *desugars*) applications of the form `(f t1 ... tn)`,
where `f` has been marked with an attribute.
This desugaring is only applied during parsing and *not* during macro expansion.
Furthermore, higher-order applications `(_ f t1 ... tn)`
do *not* recursively invoke the desugaring policy for `f`.
Note the following example.

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)

(declare-const a Bool)
(declare-const b Bool)
(define apply-f-to-ab ((f (-> Bool Bool Bool))) (f a b))
(define apply-or-to-ab () (apply-f-to-ab or))
(define apply-or-to-ab-2 () (or a b))
(define apply-or-to-ab-3 () (_ or a b))
```

In the above example, we define `or` as a right-associative nil operator.
We then define two Boolean constants `a` and `b`, and a higher-order predicate `apply-f-to-ab`
that applies a given binary predicate to these constants.
Note that since `f` is a parameter, the term `(f a b)` is parsed as an ordinary application, namely it is `(_ (_ f a) b)` after desugaring.

The definition `apply-or-to-ab`, which applies this predicate to `or`,
does *not* trigger any desugaring of `or` when it is invoked, meaning after simplification,
`apply-or-to-ab` is equivalent to `(_ (_ or a) b)`.
In constrast, definition of the predicate `apply-or-to-ab-2` involves an application of `or`,
which desugars to` (_ (_ or a) (_ (_ or b) false))`.
As a final example, the definition of predicate `apply-or-to-ab-3` is `(_ or a b)`,
which is *not* an application of `or` and hence desugars to `(_ (_ or a) b)`.

<a name="amb-functions"></a>

### Ambiguous Functions

Functions and constants that are declared via the command `declare-parameterized-const` may have return types that contain free parameters.
If these parameters are *not* contained in any explicit argument to the function, then the function or constant is considered *ambiguous*.
For example, consider a generic definition of the empty set:

```smt
(declare-const Set (-> Type Type))
(declare-parameterized-const set.empty ((T Type :implicit)) (Set T))

(declare-const Int Type)
(define f () (as set.empty (Set Int)) :type (Set Int))
```

Above, set is declared as a parameteric type.
The empty set has an implicit type argument `T` and has return type `(Set T)`.
Since `T` is a free parameter, and `set.empty` has no explicit arguments, it is an ambiguous function.
All uses of ambiguous functions must use the SMT-LIB syntax `as`,
which expects the symbol to annotate and the return type of that instance.
Above, `(as set.empty (Set Int))` refers to the instance of `set.empty` that has type `(Set Int)`.

> __Note:__ After preprocessing, the type of all ambiguous functions is automatically extended with an opaque type argument.
In the above example, `set.empty` is internally defined to be of type `(-> (Quote (Set T)) (Set T))`.
Ethos interprets `(as set.empty (Set Int))` as `(_ set.empty (Set Int))`, where this is an "opaque" application (see [opaque](#opaque)).
Conceptually, this means that `(_ set.empty (Set Int))` is a constant symbol (with no children) that is indexed by its type.

A similar treatment is given to ambiguous datatype constructors, which we describe later in [parameteric datatypes](#par-datatypes).

<a name="literals"></a>

### Literal types

The Eunoia language supports associating SMT-LIB version 3.0 syntactic categories with types. In detail, a syntax category is one of the following:

- `<numeral>` denoting the category of numerals `-?<digit>+`,
- `<decimal>` denoting the category of decimals `-?<digit>+.<digit>+`,
- `<rational>` denoting the category of rationals `-?<digit>+/<digit>+`,
- `<binary>` denoting the category of binary constants `#b<0|1>+`,
- `<hexadecimal>` denoting the category of hexadecimal constants `#x<hex-digit>+` where hexdigit is `[0-9] | [a-f] | [A-F]`,
- `<string>` denoting the category of string literals `"<char>*"`.

When parsing proofs and reference files, by default, decimal literals will be treated as syntax sugar for rational literals unless the option `--no-normalize-dec` is enabled.
Similarly, hexadecimal literals will be treated as syntax sugar for binary literals unless the option `--no-normalize-hex` is enabled.
Some SMT-LIB logics (e.g. `QF_LRA`) state that numerals should be treated as syntax sugar for rational literals.
This behavior can be enabled when parsing proofs and reference files using the option `--normalize-num`.

In contrast to SMT-LIB version 2, note that rational values can be specified directly using the syntax `5/11, 2/4, 0/1` and so on.
Rationals are normalized so that e.g. `2/4` and `1/2` are syntactically equivalent after parsing.
Similarly, decimals are normalized so that e.g. `1.300` is syntactically equivalent to `1.3` after parsing.
Note this is independent of whether these decimal values are further normalized to rational values.
In other words, by default `1.300` is syntactically equivalent to the rational `13/10`.
Also note in contrast to SMT-LIB version 2, negative arithmetic can be provided using the syntax e.g. `-1, -10.5, -1/3` and so on, instead of `(- 1), (- 10.5), (/ (- 1) 3)`.

String values use the standard escape sequences as specified in SMT-LIB version 2.6, namely `""` within a string literal denotes `"`.
The only other escape sequences are of the form `\u{dn ...d1}` for `1<=n<=5` and `\u d4 d3 d2 d1` for hexadecimal digits `d1...d5` where `d5` is in the range `[0-2]`.

> __Note:__ Numeral, rational and decimal values are implemented by the arbitrary precision arithmetic library GMP. Binary and hexadecimal values are implemented as a layer on top of numeral values that tracks a bit width. String values are implemented as a vector of unsigned integers whose maximum value is specified by SMT-LIB version 2.6, namely the character set corresponds to Unicode values 0 to 196607.

> __Note:__ The user is not required to declare that `true` and `false` are values of type `Bool`. Instead, it is assumed that the syntactic category `<boolean>` of Boolean values (`true` and `false`) has been associated with the Boolean sort. In other words, `(declare-consts <boolean> Bool)` is a part of the builtin signature assumed by Ethos.

<a name="declare-consts"></a>

#### Declaring classes of literals

The following gives an example of how to define the class of numeral constants.

```smt
(declare-const Int Type)
(declare-consts <numeral> Int)
(define P ((x Int)) (> x 7))
```

In the above example, the `declare-consts` command specifies that numerals (`1`, `2`, `3`, and so on) are constants of type `Int`.
The signature can now refer to arbitrary numerals in definitions, e.g. `7` in the definition of `P`.

> __Note:__ Internally, the command above only impacts the type rule assigned to numerals that are parsed. Furthermore, Ethos internally distinguishes whether a term is a numeral value, independently of its type, for the purposes of computational operators (see [computation](#computation)).

> __Note:__ For specifying literals whose type rule varies based on the content of the constant, the Eunoia language uses a distinguished variable `eo::self` which can be used in `declare-consts` definitions. For an example, see the type rule for SMT-LIB bit-vector constants, described later in [bv-literals](#bv-literals).

<a name="computation"></a>

## Computational Operators

Ethos has builtin support for computations over all syntactic categories of SMT-LIB version 3.0.
We list the operators below, roughly categorized by domain.
However, note that the operators are polymorphic and in some cases can be applied to multiple syntactic categories.
For example, `eo::add` returns the result of adding two integers or rationals, but also can be used to add binary constants (integers modulo a given bitwidth).
Similarly, `eo::concat` returns the result of concatenating two string literals, but can also concatenate binary constants.
We remark on the semantics in the following.

Apart from `eo::ite`, the evaluation of all operators assume that their arguments are fully reduced.
In other words, apart from `eo::ite`, all evaluation proceeds bottom-up,
where their arguments are evaluated before the builtin operator is evaluated.
For `eo::ite`, we assume that its condition is fully reduced but its branches are not evaluated until its condition is resolved.

In the following, we say a term is _ground_ if it contains no parameters as subterms.
We say a term is a _value_ if it is ground and has no occurrences of builtin operators or programs that failed to evaluate.
We say an _arithmetic value_ is a numeral, decimal or rational value.
We say a _bitwise value_ is a binary or hexadecimal value.
A 32-bit numeral value is a numeral value between `0` and `2^32-1`.
Binary values are considered to be in little endian form.

Some of the following operators can be defined in terms of the other operators.
For these operators, we provide the equivalent formulation.
A signature defining these files can be found in [derived-ops](#derived-ops).
Note, however, that the evaluation of these operators is handled by more efficient methods internally in Ethos, that is, they are not treated as syntax sugar internally.

### Core operators

- `(eo::is_ok t)`
  - If `t` is ground, this returns true if `t` is a value, and false otherwise. If `t` is not ground, it does not evaluate.

- `(eo::ite t1 t2 t3)`
  - Returns `t2` if `t1` is `true`, `t3` if `t1` is `false`, and is not evaluated otherwise. Note that the branches of this term are only evaluated if they are the return term.

- `(eo::eq t1 t2)`
  - If `t1` and `t2` are ground values, this returns `true` if `t1` is (syntactically) equal to `t2` and `false` otherwise. If either `t1` or `t2` is non-ground, it does not evaluate. Note this can be expressed as an ordinary Eunoia program as we describe in [derived-ops](#derived-ops).

- `(eo::is_eq t1 t2)`
  - Equivalent to `(eo::ite (eo::and (eo::is_ok t) (eo::is_ok s)) (eo::eq s t) false)`.

- `(eo::requires t1 t2 t3)`
  - Returns `t3` if `(eo::is_eq t1 t2)` evaluates to `true`, and is not evaluated otherwise. In the case this operator evaluates, it may be the case that `t3` is non-ground.

- `(eo::hash t1)`
  - If `t1` is a value, this returns a numeral that is unique to `t1`.
- `(eo::typeof t1)`
  - If `t1` is a value, this returns the type of `t1` if its type is ground.
- `(eo::nameof t1)`
  - If `t1` is a ground constant or variable, this returns the name of `t1`, i.e. the string corresponding to the symbol it was declared with.
- `(eo::var t1 t2)`
  - If `t1` is a string value and `t2` is a ground type, this returns the variable whose name is `t1` and whose type is `t2`.
- `(eo::cmp t1 t2)`
  - Equivalent to `(eo::is_neg (eo::add (eo::neg (eo::hash t1)) (eo::hash t2)))`. Note that this method corresponds to an arbitrary total order on terms.
- `(eo::is_z t)`
  - Equivalent to `(eo::is_eq (eo::to_z t) t)`.
- `(eo::is_q t)`
  - Equivalent to `(eo::is_eq (eo::to_q t) t)`. Note this returns false for decimal literals.
- `(eo::is_bin t)`
  - Equivalent to `(eo::is_eq (eo::to_bin (eo::len t) t) t)`. Note this returns false for hexadecimal literals.
- `(eo::is_str t)`
  - Equivalent to `(eo::is_eq (eo::to_str t) t)`.
- `(eo::is_bool t)`
  - Equivalent to `(eo::or (eo::is_eq t true) (eo::is_eq t false))`.
- `(eo::is_var t)`
  - Equivalent to `(eo::is_eq (eo::var (eo::nameof t) (eo::typeof t)) t)`.

### Boolean operators

- `(eo::and t1 t2)`
  - Boolean conjunction if `t1` and `t2` are Boolean values (`true` or `false`).
  - Bitwise conjunction if `t1` and `t2` are bitwise values of the same category and bitwidth.
- `(eo::or t1 t2)`
  - Boolean disjunction if `t1` and `t2` are Boolean values.
  - Bitwise disjunction if `t1` and `t2` are bitwise values of the same category and bitwidth.
- `(eo::xor t1 t2)`
  - Boolean xor if `t1` and `t2` are Boolean values.
  - Bitwise xor if `t1` and `t2` are bitwise values of the same category and bitwidth.
- `(eo::not t1)`
  - Boolean negation if `t1` is a Boolean value.
  - Bitwise negation if `t1` is a bitwise value.

### Arithmetic operators

- `(eo::add t1 t2)`
  - If `t1` and `t2` are arithmetic values of the same category, then this returns the addition of `t1` and `t2`.
  - If `t1` and `t2` are bitwise values of the same category and bitwidth, this returns the binary value corresponding to their (unsigned) addition modulo their bitwidth.
- `(eo::mul t1 t2)`
  - If `t1` and `t2` are arithmetic values of the same category, then this returns the multiplication of `t1` and `t2`.
  - If `t1` and `t2` are bitwise values of the same category and bitwidth, this returns the binary value corresponding to their (unsigned) multiplication modulo their bitwidth.
- `(eo::neg t1)`
  - If `t1` is a arithmetic value, this returns the arithmetic negation of `t1`.
  - If `t1` is a binary value, this returns its (signed) arithmetic negation.
- `(eo::qdiv t1 t2)`
  - If `t1` and `t2` are values of the same category and `t2` is non-zero, then this returns the rational division of `t1` and `t2`.
- `(eo::zdiv t1 t2)`
  - If `t1` and `t2` are numeral values and `t2` is non-zero, then this returns the integer division (floor) of `t1` and `t2`.
  - If `t1` and `t2` are bitwise values of the same category and bitwidth, then this returns their (total, unsigned) division, where division by zero returns the max unsigned value.
- `(eo::zmod t1 t2)`
  - If `t1` and `t2` are numeral values and `t2` is non-zero, then this returns the integer remainder of `t1` and `t2`.
  - If `t1` and `t2` are bitwise values of the same category and bitwidth, then this returns their (total, unsigned) remainder, where remainder by zero returns `t1`.
- `(eo::is_neg t1)`
  - If `t1` is an arithmetic value, this returns `true` if `t1` is strictly negative and `false` otherwise. Otherwise, this operator is not evaluated.
- `(eo::gt t1 t2)`
  - Equivalent to `(eo::is_neg (eo::add (eo::neg t1) t2))`.

### String operators

- `(eo::len t1)`
  - Binary length (bitwidth) if `t1` is a binary value.
  - String length if `t1` is a string value.
- `(eo::concat t1 t2)`
  - The concatenation of bits if `t1` and `t2` are binary values.
  - The concatenation of strings if `t1` and `t2` are string values.
- `(eo::extract t1 t2 t3)`
  - If `t1` is a binary value and `t2` and `t3` are numeral values, this returns the binary value corresponding to the bits in `t1` from position `t2` through `t3` if `0<=t2`, or the empty binary value otherwise.
  - If `t1` is a string value and `t2` and `t3` are numeral values, this returns the string value corresponding to the characters in `t1` from position `t2` through `t3` inclusive if `0<=t2`, or the empty string value otherwise.
- `(eo::find t1 t2)`
  - If `t1` and `t2` are string values, this returns a numeral value corresponding to the first index (left to right) where `t2` occurs as a substring of `t1`, or the numeral value `-1` otherwise.

### Conversion operators

- `(eo::to_z t1)`
  - If `t1` is a numeral value, return `t1`.
  - If `t1` is a rational value, return the numeral value corresponding to the floor of `t1`.
  - If `t1` is a binary value, this returns the numeral value corresponding to `t1`.
  - If `t1` is a string value of length one, this returns the code point of its character.
- `(eo::to_q t1)`
  - If `t1` is a rational value, return `t1`.
  - If `t1` is a numeral value, this returns the (integral) rational value that is equivalent to `t1`.
- `(eo::to_bin t1 t2)`
  - If `t1` is a 32-bit numeral value and `t2` is a binary value, this returns a binary value whose value is `t2` and whose bitwidth is `t1`.
  - If `t1` is a 32-bit numeral value and `t2` is a non-negative numeral value, return the binary value whose value is `t2` (modulo `2^t1`) and whose bitwidth is `t1`.
- `(eo::to_str t1)`
  - If `t1` is a string value, return `t1`.
  - If `t1` is a numeral value specifying a code point from Unicode planes `0-2` (i.e. a numeral between `0` and `196607`), return the string of length one whose character has code point `t1`.
  - If `t1` is a rational or binary value, return the string value corresponding to the result of printing `t1`. 
  - If `t1` is a hexadecimal value, return the string value corresponding to the result of printing `t1`. This will use lowercase letters for digits greater than `9`.
  - If `t1` is a decimal value, return the string value corresponding to the result of printing `t1` as a rational.

Ethos eagerly evaluates ground applications of computational operators.
In other words, the term `(eo::add 1 1)` is syntactically equivalent in all contexts to `2`.

Currently, apart from applications of `eo::ite`, all terms are evaluated bottom-up.
This means that e.g. in the evaluation of `(eo::or A B)`, both `A` and `B` are always evaluated even if `A` evaluates to `true`.

Ethos supports extensions of `eo::and, eo::or, eo::xor, eo::add, eo::mul, eo::concat` to an arbitrary number of arguments `>=2`.

### Computation Examples

```smt
(eo::and true false)        == false
(eo::and #b1110 #b0110)     == #b0110
(eo::or true false)         == true
(eo::xor true true)         == false
(eo::xor #b111 #b011)       == #b100
(eo::not true)              == false
(eo::not #b1010)            == #b0101
(eo::add 1 1)               == 2
(eo::add 1 1 1 0)           == 3
(eo::add 1/2 1/3)           == 5/6
(eo::add 2 1/3)             == (eo::add 2 1/3)  ; no mixed arithmetic
(eo::add 2/1 1/3)           == 7/3
(eo::add 2.0 1/3)           == (eo::add 2.0 1/3)  ; since no mixed arithmetic
(eo::add 2.0 2.5)           == 4.5
(eo::add #b01 #b01)         == #b10
(eo::add #x1 #b0001)        == (eo::add #x1 #b0001)  ; since no mixed arithmetic
(eo::mul 2 7)               == 14
(eo::mul 2 2 7)             == 28
(eo::mul 1/2 1/4)           == 1/8
(eo::neg -15)               == 15
(eo::qdiv 12 6)             == 3/1
(eo::qdiv 7 2)              == 7/2
(eo::qdiv 7/1 2/1)          == 7/2
(eo::qdiv 7.0 2.0)          == 7/2
(eo::qdiv 7 0)              == (eo::qdiv 7 0)  ; no division by zero
(eo::zdiv 12 3)             == 4
(eo::zdiv 7 2)              == 3
(eo::is_neg 0)              == false
(eo::is_neg -7/2)           == true
(eo::len "abc")             == 3
(eo::len """hi""")          == 4
(eo::len "\u{AB0E}")        == 1
(eo::len "\uA")             == 3
(eo::len #b11100)           == 5
(eo::concat "abc" "def")    == "abcdef"
(eo::concat #b000 #b11)     == #b00011
(eo::extract "abcdef" 0 1)  == "ab"
(eo::extract "abcdef" -1 3) == ""
(eo::extract "abcdef" 1 10) == "bcdef"
(eo::extract #b11100 2 4)   == #b111
(eo::extract #b11100 2 1)   == #b
(eo::extract #b111000 1 10) == #b11100
(eo::extract #b10 -1 2)     == #b
(eo::find "abc" "bc")       == 1
(eo::find "abc" "")         == 0
(eo::find "abcdef" "g")     == -1
(eo::to_z 3/2)              == 1
(eo::to_z 45)               == 45
(eo::to_z "A")              == 65
(eo::to_z "1")              == 49
(eo::to_z "451")            == (eo::to_z "451")  ; string is not length one
(eo::to_z "")               == (eo::to_z "")  ; string is not length one
(eo::to_z "\u{9876}")       == 9876
(eo::to_q 6)                == 6/1
(eo::to_bin 4 3)            == #b0011
(eo::to_bin 4 #b1)          == #b0001
(eo::to_bin 2 #b10101010)   == #b10
(eo::to_str 65)             == "A"
(eo::to_str 123)            == "{"
(eo::to_str -1)             == (eo::to_str -1) ; since not a valid code point
(eo::to_str 200000)         == (eo::to_str 200000) ; since not a valid code point
(eo::to_str 1/2)            == "1/2"
(eo::to_str #b101)          == "#b101"
```

### Core Computation Examples

Note the following examples of core operators for the given signature

```smt
(declare-const Int Type)
(declare-const x Int)
(declare-const y Int)
(declare-const a Bool)

(eo::is_ok 0)                        == true
(eo::is_ok (eo::neg "abc"))          == false

(eo::eq x x)                         == true
(eo::eq 0 1)                         == false
(eo::eq x y)                         == false
(eo::eq (eo::neg "a") x)             == (eo::eq (eo::neg "a") x)              ; since the first argument fails to evaluate
(eo::eq (eo::neg "a") (eo::neg "a")) == (eo::eq (eo::neg "a") (eo::neg "a"))  ; since both arguments fail to evaluate
(eo::eq 2 (eo::add 1 1))             == true

(eo::is_eq x x)                         == true
(eo::is_eq 0 1)                         == false
(eo::is_eq x y)                         == false
(eo::is_eq (eo::neg "a") x)             == false
(eo::is_eq (eo::neg "a") (eo::neg "a")) == false
(eo::is_eq 2 (eo::add 1 1))             == true

(eo::ite false x y)                  == y
(eo::ite true Bool Int)              == Bool
(eo::ite a x x)                      == (eo::ite a x x)  ; a is not a value
(eo::ite (eo::eq x 1) x y)           == y

(eo::requires x 0 true)              == (eo::requires x 0 true)  ; x and 0 are not syntactically equal
(eo::requires x x y)                 == y
(eo::requires x x Int)               == Int
```

In the above, it is important to note that `eo::eq` and `eo::is_eq` are checks for syntactic equality, which is different from saying the terms are semantically distinct in all models.
For example `(eo::eq x y)` returns `false`.

<a name="list-computation"></a>

## List computations

Below, we assume that `f` is right associative operator with nil terminator `nil` and `t1, t2` are values. Otherwise, the following operators do not evaluate.
We describe the evaluation for right associative operators; left associative evaluation is defined analogously.
We say that a term is an `f`-list with children `t1 ... tn` if it is of the form `(f t1 ... tn)` where `n>0` or `nil` if `n=0`.

Note that all of the list operators here (with the exception of `eo::nil`) have a semantics that can be described as an ordinary Eunoia program.
We describe a signature that gives these definitions in [derived-ops](#derived-ops).

### List operators

- `(eo::nil f T)`
  - If `f` is a right associative operator and `T` is a ground type, return its nil terminator. If `f` has a parametric nil terminator, return the terminator is specialized for `T` (see examples of parametric nil terminators later in this section).
- `(eo::cons f t1 t2)`
  - If `t2` is an `f`-list, then this returns the term `(f t1 t2)`.
- `(eo::list_len f t)`
  - If `t` is an `f`-list with children `t1 ... tn`, then this returns `n`.
- `(eo::list_concat f t1 t2)`
  - If `t1` is an `f`-list with children `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, this returns `(f t11 ... t1n t21 ... t2m)` if `n+m>0` and `nil` otherwise. Otherwise, this operator does not evaluate.
- `(eo::list_nth f t1 t2)`
  - If `t1` is `(f s0 ... s{n-1})` and `t2` is a numeral value such that `0<=t2<n`, then this returns `s_{t2}`. Otherwise, this operator does not evaluate.
- `(eo::list_find f t1 t2)`
  - If `t1` is `(f s0 ... s{n-1})`, then this returns the smallest numeral value `i` such that `t2` is syntactically equal to `si`, or `-1` if no such `si` can be found. Otherwise, this operator does not evaluate.
- `(eo::list_rev f t1)`
  - If `t1` is an `f`-list with children `t11 ... t1n`, then this returns `(f t1n ... t11)`.
- `(eo::list_erase f t1 t2)`
  - If `t1` is an `f`-list, then this returns the result of removing the first occurrence of `t2` from `t1` if it exists. Returns `t1` unchanged if it does not contain `t2`.
- `(eo::list_erase_all f t1 t2)`
  - If `t1` is an `f`-list, then this returns the result of removing all occurrences of `t2` from `t1`, where the remaining elements are kept in order. Returns `t1` unchanged if it does not contain `t2`.
- `(eo::list_setof f t1)`
  - If `t1` is an `f`-list with children `t11 ... t1n`, this returns the `f`-list obtained by dropping each element from this list beyond the first occurrence. Note that the remaining elements are kept in order.
- `(eo::list_minclude f t1 t2)`
  - (Multiset inclusion) If `t1` is an `f`-list with children `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, then this returns true if each unique element in `t11 ... t1n` occurs with the greater than or equal multiplicity in `t21 ... t2m`. Note that order of the elements does not matter.
- `(eo::list_meq f t1 t2)`
  - (Multiset equal) Equivalent to `(eo::and (eo::list_minclude f t1 t2) (eo::list_minclude t2 t1))`.
- `(eo::list_diff f t1 t2)`
  - (Difference) If `t1` is an `f`-list with children `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, this returns the result of erasing elements of `t11 ... t1n` that occur in `t21 ... t2m` where multiplicity is considered. In detail, for each `i = 1, ..., n`, if `t1i` occurs in `t21 ... t2m`, we remove one copy of it from that list. Otherwise if `t1i` does not occur in `t21 ... t2m`, we append it to the final result.
- `(eo::list_inter f t1 t2)`
  - (Intersection) If `t1` is an `f`-list with children `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, this returns the result of erasing elements of `t11 ... t1n` that do not occur in `t21 ... t2m` where multiplicity is considered. In detail, for each `i = 1, ..., n`, if `t1i` occurs in `t21 ... t2m`, we erase one copy of it from that list and append it to the final result.
- `(eo::list_singleton_elim f t1)`
  - (Singleton elimination) If `t1` is an `f`-list containing a single child `t11`, this returns `t11`. All other `f`-lists `t1` are returned unchanged. Otherwise, this operator does not evaluate.

### List Computation Examples

The terms on both sides of the given evaluation are written in their form prior to desugaring, where recall that e.g. `(or a)` after desugaring is `(or a false)` and `(or a b)` is `(or a (or b false))`.

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)

(eo::nil or Bool)                   == false
(eo::nil a Bool)                    == (eo::nil a Bool)                ; since a is not an associative operator

(eo::cons or a (or a b))            == (or a a b)
(eo::cons or false (or a b))        == (or false a b)
(eo::cons or (or a b) (or b))       == (or (or a b) b)
(eo::cons or false false)           == (or false)
(eo::cons or a b)                   == (eo::cons or a b)                ; since b is not an or-list
(eo::cons or a (or b))              == (or a b)
(eo::cons and (or a b) (and b))     == (and (or a b) b)
(eo::cons and true (and a))         == (and a)
(eo::cons and (and a) true)         == (and (and a))

(eo::list_len or (or a b))          == 2
(eo::list_len or (or (or a a) b))   == 2
(eo::list_len or false)             == 0
(eo::list_len or (and a b))         == (eo::list_len or (and a b))  ; since (and a b) is not an or-list

(eo::list_concat or false false)            == false
(eo::list_concat or (or a b) (or b))        == (or a b b)
(eo::list_concat or (or (or a a)) (or b))   == (or (or a a) b)
(eo::list_concat or false (or b))           == (or b)
(eo::list_concat or (or a b b) false)       == (or a b b)
(eo::list_concat or a (or b))               == (eo::list_concat or a (or b))         ; since a is not an or-list
(eo::list_concat or (or a) b)               == (eo::list_concat or (or a) b)         ; since b is not an or-list
(eo::list_concat or (or a) (or b))          == (or a b)
(eo::list_concat or (and a b) false)        == (eo::list_concat or (and a b) false)  ; since (and a b) is not an or-list

(eo::list_nth or (or a b a) 1)            == b
(eo::list_nth or (or a) 0)                == a
(eo::list_nth or false 0)                 == (eo::list_nth or false 0)         ; since false has <=0 children
(eo::list_nth or (or a b a) 3)            == (eo::list_nth or (or a b a) 3)    ; since (or a b a) has <=3 children
(eo::list_nth or (and a b b) 0)           == (eo::list_nth or (and a b b) 0)   ; since (and a b b) is not an or-list

(eo::list_find or (or a b a) b)           == 1
(eo::list_find or (or a b a) true)        == -1
(eo::list_find or (and a b b) a)          == (eo::list_find or (and a b b) a)      ; since (and a b b) is not an or-list

(eo::list_rev or (or a b c))              == (or c b a)
(eo::list_rev or false)                   == false

(eo::list_erase or (or a b c) a)          == (or b c)
(eo::list_erase or (or c a a b a) a)      == (or c a b a)
(eo::list_erase or (or a b c) d)          == (or a b c)
(eo::list_erase or false d)               == false

(eo::list_erase_all or (or a b c) a)          == (or b c)
(eo::list_erase_all or (or a a b a) a)        == (or b)
(eo::list_erase_all or (or a b c) d)          == (or a b c)
(eo::list_erase_all or false d)               == false

(eo::list_setof or (or a b c))            == (or a b c)
(eo::list_setof or (or a b a c a b c))    == (or a b c)
(eo::list_setof or (or a a a))            == (or a)
(eo::list_setof or false)                 == false

(eo::list_minclude or (or a b) (or a a b))  == true
(eo::list_minclude or (or a b) (or b a))    == true
(eo::list_minclude or (or a b b) (or a b))  == false
(eo::list_minclude or false (or a b))       == true

(eo::list_meq or (or a b) (or a a b))       == false
(eo::list_meq or (or a b c b) (or b a c b)) == true
(eo::list_meq or (or a b b) (or a a b))     == false
(eo::list_meq or false false)               == true

(eo::list_diff or (or a b) (or a a b))      == false
(eo::list_diff or (or a a b) (or a b))      == (or a)
(eo::list_diff or (or a b c b a) (or c b))  == (or a b a)
(eo::list_diff or (or a b a c a) (or a a))  == (or b c a)

(eo::list_inter or (or a b) (or a a b))     == (or a b)
(eo::list_inter or (or a a b) (or a b))     == (or a b)
(eo::list_inter or (or a b c b a) (or c b)) == (or b c)
(eo::list_inter or (or a b a c a) (or a a)) == (or a a)

(eo::list_singleton_elim or (or a b c))     == (or a b c)
(eo::list_singleton_elim or (or a a a))     == (or a a a)
(eo::list_singleton_elim or (or a))         == a
```

### Parametric Nil terminators

As we will introduce in [param-constants](#param-constants),
`eo::nil` accepts a type argument in addition to the operator.
For example, `(eo::nil bvor (BitVec 4))` denotes the nil terminator of `bvor` whose type is `(BitVec 4)`.

### Example: Type rule for BitVector concatenation

```smt
(declare-const Int Type)
(declare-consts <numeral> Int)
(declare-const BitVec (-> Int Type))

(declare-parameterized-const concat ((n Int :implicit) (m Int :implicit))
  (->
  (BitVec n)
  (BitVec m)
  (BitVec (eo::add n m))))

(declare-const x (BitVec 2))
(declare-const y (BitVec 3))
(define z () (concat x y) :type (BitVec 5))
```

Above, we define a type declaration for `BitVec` that expects an integer (i.e. denoting the bitwidth) as an argument.
Then, a type rule is given for bitvector concatenation `concat`, involves the result of invoking `eo::add` on the bitwidth of its two arguments.

Since `eo::add` only evaluates on numeral values, this means that this type rule will only give the intended result when the bitwidth arguments to this function are concrete.
If on the other hand we defined:

```smt
...
(declare-const a Int)
(declare-const b Int)
(declare-const x2 (BitVec a))
(declare-const y2 (BitVec b))
(define z2 () (concat x2 y2) :type (BitVec (eo::add a b)))
```

Based on the definition of `concat`, the return type of `z2` in the above example is `(BitVec (eo::add a b))`, where the application of `eo::add` does not evaluate since `a` and `b` are not values.
However, any term with a type that is both ground (i.e. containing no parameters) and evaluatable (i.e. containing an application of a program or builtin evaluation operator) is considered ill-typed by Ethos.
Hence, the above example results in a type checking error.
This was not the case with `z` in the previous example, whose type prior to evaluation was`(BitVec (eo::add 2 3))`, which evaluates to `(BitVec 5)` which is a legal type.

<a name="bv-literals"></a>

### Example: Type rule for BitVector constants

```smt
(declare-const Int Type)
(declare-consts <numeral> Int)
(declare-const BitVec (-> Int Type))

(declare-consts <binary> (BitVec (eo::len eo::self)))

(define x () #b000 :type (BitVec 3))
```

To define the class of binary values, whose type depends on the number of bits they contain, Ethos provides support for a distinguished parameter `eo::self`.
The type checker for values applies the substitution mapping `eo::self` to the term being type checked.
This means that when type checking the binary constant `#b0000`, its type prior to evaluation is `(BitVec (eo::len #b0000))`, which evaluates to `(BitVec 4)`.

<a name="param-constants"></a>

## Parameterized constants with Attributes

Recall that in [assoc-nil](#assoc-nil), when using `declare-const` to define associative operators with nil terminators, it is not possible to have the nil terminator for that operator depend on its type parameters.
In this section, we note that `declare-parameterized-const` which overcomes this limitation.

In the following example,
we declare bitvector-or (`bvor` in SMT-LIB) where its nil terminator is bitvector zero for the given bitwidth.

```smt
(declare-const Int Type)
(declare-consts <numeral> Int)                ; numeral literals denote Int constants
(declare-const BitVec (-> Int Type))
(declare-consts <binary>
    (BitVec (eo::len eo::self)))              ; binary literals denote BitVec constants of their length
(define bvzero ((m Int)) (eo::to_bin m 0))    ; returns the bitvector value zero for bitwidth m

(declare-parameterized-const bvor ((m Int :implicit))   ; bvor is parameterized by a bitwidth m
    (-> (BitVec m) (BitVec m) (BitVec m))
    :right-assoc-nil (bvzero m)               ; its nil terminator depends on m
)
```

In this example, we first declare the `Int` and `BitVec` sorts, and associate numeral and binary values with those sorts (see [declare-consts](#declare-consts)).
Then, we declare `bvor` using `declare-parameterized-const` where its parameter is an integer `m`.
The provided parameters are in scope for the remainder of the command, which means they can appear in the nil terminator of the operator.
Here, we specify `(bvzero m)` as the nil terminator for `bvor`.

The parameter list of a parameterized constant may either be implicit or explicit arguments.
In this example, the argument `m` to `bvor` is implicit.
Thus, it expects two bit-vectors of the same width and returns a bit-vector of that width.

> __Note:__ Parameterized constants that have non-ground nil terminators are required to have type `(-> T T T)`.

If a function `f` is given a nil terminator with free parameters, this impacts:

- how applications of `f` are desugared, and
- how `eo::nil` is computed for `f`.

For the former, say we apply `(f t1 ... tn)`, where `f` is right associative with nil terminator `nil` whose type is _not_ ground.
Similar to the procedure described in [assoc-nil](#assoc-nil),
if `tn` is not marked with `:list`, we insert a term corresponding to the nil terminator of `f` to the end of the argument list.
However, since `nil` is not ground, we use the term `(eo::nil f (eo::typeof t1))` instead of `nil` itself.
This term is a placeholder for the nil terminator of the appropriate type, as determined by the type of the term we are constructing.
Note that we use the first term `t1` in the argument list, as operators with non-ground nil terminators are required to be of type `(-> T T T)`, meaning that a single argument suffices to determine its parameters.

For the latter, to handle parameteric nil terminators,
`eo::nil` optionally accepts two arguments (the function and the return type of the nil terminator).
For each declared function `f` of type `(-> T T T)` with nil terminator `nil`,
we assume there is a case of `eo::nil` that matches the pair `(f, T)` and whose specified return is (non-ground term) `nil`,
where notice that the free parameters of `nil` are expected to be contained in the free parameters of `T`.
For example, for `bvor`, a case of `eo::nil` would map
`(eo::nil bvor (BitVec m))` to `(bvzero m)`, where `m` is bound based on the provided (concrete) bit-vector type.

Examples of this are given in the following, assuming the declaration of `bvor` above.

```smt
(declare-const p (-> Bool Bool))
(define test ((x (BitVec 4)) (y (BitVec 4)) (n Int) (z (BitVec n)) (w (BitVec n)) (u (BitVec n) :list))
    ...
    (bvor z w)        ; (bvor z (bvor w (eo::nil bvor (eo::typeof z))))
    (bvor z u)        ; (bvor z u)
    (bvor u z)        ; (eo::list_concat bvor u (bvor z (eo::nil bvor (eo::typeof u))))
    (bvor x y)        ; (bvor x (bvor y #b0000))
    (bvor x)          ; (bvor x #b0000)
    ...
)
```

Above, notice that `x` and `y` have concrete bitwidths and `z,w,u` have the free parameter `n` as their bitwidth.

In the first example, since `w` is not marked as a list and `bvor` has a non-ground nil terminator,
we insert the nil terminator `(eo::nil bvor (eo::typeof z))`,
which notice does _not_ evaluate since `z` has non-ground type `(BitVec n)`.
In the second example, `(bvor z u)` is also type checked to `(BitVec n)`,
but in this case the nil terminator is not used since `u` is marked as `:list`.
In the third example, we use `eo::list_concat` as before since the list term `u` appears as the first argument.
Similar to the third example, a placeholder for the nil terminator is generated.

In the fourth example,
we have that `y` is not marked as a list and thus
we insert the nil terminator `(eo::nil bvor (eo::typeof x))`.
In contrast to the previous examples, `x` has ground type `(BitVec 4)`
and hence this simplifies to `(eo::nil bvor (BitVec 4))`,
which furthermore evaluates to `#b0000`.
The fifth example is similar, for the case of a singleton list.

Consider again the term `(bvor z w)` from the previous example:

```smt
(define test ((n Int :implicit) (z (BitVec n)) (w (BitVec n)))
  (bvor z w)        ; (bvor z (bvor w (eo::nil bvor (eo::typeof z))))
)
(declare-const a (BitVec 4))
(declare-const b (BitVec 4))
(define test4 () (test a b) :type (BitVec 4))
```

The term in the body of `test` desugars to `(bvor z (bvor w (eo::nil bvor (eo::typeof z))))`, where
`(eo::nil bvor (eo::typeof z))` does not evaluate since `z` has non-ground type.
In this example, we instantiate this definition in the body of `test4`, where `z=a` and `w=b`.
The term `(bvor a (bvor b (eo::nil bvor (eo::typeof a))))` then evaluates to `(bvor a (bvor b #b0000)`,
noting that `(eo::nil bvor (eo::typeof a))` evaluates to `#b0000`.

The following are examples of list operations when using parameterized constant `bvor`:

```smt
(declare-const a (BitVec 4))
(declare-const b (BitVec 4))
(declare-const c (BitVec 5))

(eo::nil bvor)                == (eo::nil bvor)     ; since we cannot infer the type of bvor
(eo::nil bvor (BitVec 4))     == #b0000
(eo::nil bvor (BitVec 5))     == #b00000

(eo::cons bvor a #b0000)            == (bvor a)
(eo::cons bvor a (bvor a b))        == (bvor a a b)

(eo::list_concat bvor #b0000 #b0000)       == #b0000
(eo::list_concat bvor (bvor a b) (bvor b)) == (bvor a b b)
```

> __Note:__ If no free parameters are used in the nil terminator of a parameterized constant, then no special handling of the nil element of that function is necessary. In particular, this means that all applications of the `eo::nil` are eagerly replaced by the (ground) nil terminator.

<a name="overloading"></a>

## Overloading

Ethos supports symbol overloading.
For example, the following is accepted:

```smt
(declare-const - (-> Int Int))
(declare-const - (-> Int Int Int))
(declare-const - (-> Real Real Real))
```

When parsing a term whose head is `-`, Ethos will automatically choose which symbol to use based on the arguments passed to it.
In particular, if a symbol is overloaded, Ethos will use the first symbol that results in a well-typed term if applied.
For example, assuming standard definitions of SMT-LIB literal values,
`(- 1)` uses the first, `(- 0 1)` uses the second, and `(- 0.0 1.0)` uses the third.
If a symbol is unapplied, then Ethos will interpret it as the first declared term for that symbol.

> __Note:__ When multiple variants are possible, Ethos will use the first one and will _not_ throw a warning. This behavior permits the user to order the declarations in the order of their precedence. For example, the SMT-LIB operator for unary negation should be declared _before_ the declaration for subtraction. If this were done in the opposite order, then (- t) would be interpreted as the partial application of subtraction to the term t.

Furthermore, Ethos supports an operator `eo::as` for disambiguation whose syntax is `(eo::as <term><type>)`.
A term of the form `(eo::as t (-> T1 ... Tn T))` evaluates to term `s` only if `(s k1 ... kn)` has type `T` where `k1 ... kn` are variables of type `T1 ... Tn`, and `t` and `s` are atomic terms with the same name.
If multiple such terms `s` exist, then the most recent one is returned.
Otherwise, the term `(eo::as t (-> T1 ... Tn T))` is unevaluated.
For example, `(eo::as - (-> Int Int Int))` evaluates to the second declared symbol in the example above.

<a name="datatypes"></a>

## Generic Reasoning about Datatypes

Eunoia has support for retrieving the list of constructors associated with a datatype, as well as the list of selectors associated with a datatype constructor.
This allows one to write side conditions and proof rules that reason about datatypes in a generic way, independent of the specific instance of the datatype.

In particular, Eunoia has support for:
- `(eo::dt_constructors T)`
  - If `T` is a datatype type (that is, `T` was declared via `declare-datatype` or `declare-datatypes` command), then this returns the list (see below) of constructors for that type. Otherwise this operator does not evaluate.
- `(eo::dt_selectors c)`
  - If `c` is a datatype constructor (that is, `c` was declared as a constructor within a `declare-datatype` or `declare-datatypes` command), then this returns the list of selectors of that constructor. Otherwise this operator does not evaluate.

In detail, for the purposes of representing the return value of these operators, Eunoia assumes the definition of a type `eo::List` with constructors `eo::List::nil` and `eo::List::cons`, where the latter is right associative with the former as its nil terminator. In other words, the following commands can be assumed as part of the builtin signature assumed by Ethos:

```smt
(declare-const eo::List Type)
(declare-const eo::List::nil eo::List)
(declare-parameterized-const eo::List::cons ((T Type :implicit))
  (-> T eo::List eo::List)
  :right-assoc-nil eo::List::nil)
```

> __Note:__ `eo::List` is not itself a datatype type.

The constructor `eo::List::cons` is heterogeneous in that terms of any type can be included in the same list.
Given a datatype with constructors `c_1 ... c_n`, the `eo::dt_constructors` will return the term `(eo::List::cons c_1 ... c_n)`.
Examples of these operators are given below.

```smt
(declare-datatypes ((Tree 0)) (((node (left Tree) (right Tree)) (leaf))))

(eo::dt_constructors Tree)   == (eo::List::cons node (eo::List::cons leaf eo::List::nil))
(eo::dt_selectors node)      == (eo::List::cons left (eo::List::cons right eo::List::nil))
(eo::dt_selectors leaf)      == eo::List::nil

(declare-datatypes ((Color 0)) (((red) (green) (blue))))

(eo::dt_constructors Color)   == (eo::List::cons red (eo::List::cons green (eo::List::cons blue eo::List::nil)))
(eo::dt_selectors red)        == eo::List::nil

```

<a name="dt-split"></a>

### Example: A generic splitting rule for Datatypes

The following declares a generic proof rule for splitting on the top constructor symbol of a term of datatype type.
We assume the declaration of a generic `is` predicate (often called a "tester" predicate) which takes as input a constructor symbol and a datatype term.

```smt

; The constraint (is c x) is true iff x is an application of constructor c
(declare-parameterized-const is ((C Type :implicit) (D Type :implicit)) (-> C D Bool))

(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)

(program $mk_dt_split ((D Type) (x D) (T Type) (c T) (xs eo::List :list))
  :signature (eo::List D) Bool
  (
    (($mk_dt_split eo::List::nil x)          false)
    (($mk_dt_split (eo::List::cons c xs) x)  (eo::cons or (is c x) ($mk_dt_split xs x)))
  )
)

(declare-rule dt-split ((D Type) (x D))
  :args (x)
  :conclusion ($mk_dt_split (eo::dt_constructors (eo::typeof x)) x)
)

(declare-datatypes ((Tree 0)) (((node (left Tree) (right Tree)) (leaf))))

(declare-const x Tree)
(step @p0 (or (is node x) (is leaf x)) :rule dt-split :args (x))

(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-const y Color)
(step @p1 (or (is red y) (is green y) (is blue y)) :rule dt-split :args (y))
```

In this example, after declaring our tester predicate `is`, we introduce a side condition `$mk_dt_split` that is used for defining a proof rule `dt-split`.
The side condition recurses over a list of constructors, which was obtained in the definition of the proof rule from applying `eo::dt_constructors` to the type of `x`.
For each constructor `c` in this list, we prepend a disjunct `(is c x)` to a recursive call to this method.

As part of the example, we see a particular definition of a list, called `Tree`.
Applying the proof rule `dt-split` to a variable `x` of type `Tree` allows us to conclude that `x` must either be an application of `node` or `leaf`.
Note that the definitino of `dt-split` is applicable to *any* datatype definition.
In particular, as a second example, we see the rule applied to a term `y` of type `Color` gives us a conclusion with three disjuncts.


<a name="par-datatypes"></a>

### Parametric datatypes

Ethos supports reasoning about parametric datatypes with ambiguous datatype construtors using the same syntax as SMT-LIB 2.6.

In detail, we say a datatype constructor is "ambiguous" if it of type:
```
(-> T1 ... Tn T)
```
where some free parameter of T is not contained in the free parameters of `T1, ..., Tn`. (Note `n` may be 0).

All ambiguous datatype constructors are required to be annotated using the SMT-LIB 2.6 syntax `(as <constructor> <type>)`.
For example:
```
(declare-datatypes ((Tree 1)) ((par (X) (((node (left Tree) (data X) (right Tree)) (leaf))))))
```
In the this example, `leaf` is an ambiguous datatype constructor, while `node` is not.
Instances of ambiguous datatype constructors are expected to be annotated with their return type using the syntax e.g. `(as leaf (Tree Int))`.
This denotes a constant (e.g. a term with zero arguments), whose type is `(Tree Int)`.

> __Note:__ Internally, all ambiguous datatype constructors are instead defined to be of type `(-> (Quote T) T1 ... Tn T)`
This is done automatically, so that for the aforementioned datatype, the type of `leaf` is `(-> (Quote (Tree X)) (Tree X))`.
Ethos interprets `(as leaf (Tree Int))` as `(_ leaf (Tree Int))`, where this is an "opaque" application (see [opaque](#opaque)).
Conceptually, this means that `(_ leaf (Tree Int))` is a constant symbol (with no children) that is indexed by its type.

The semantics of `eo::dt_constructors` and `eo::dt_selectors` is overloaded to handle (annotated) constructors and (instantiated) parameteric datatypes.
For example, given the previous definition, note the following:
```
(eo::dt_constructors Tree)              == (eo::List::cons node (eo::List::cons leaf eo::List::nil))
(eo::dt_constructors (Tree Int))        == (eo::List::cons node (eo::List::cons (as leaf (Tree Int)) eo::List::nil))
(eo::dt_constructors (Tree U))          == (eo::List::cons node (eo::List::cons (as leaf (Tree U)) eo::List::nil))

(eo::dt_selectors node)                 == (eo::List::cons left (eo::List::cons data (eo::List::cons right eo::List::nil)))
(eo::dt_selectors leaf)                 == eo::List::nil
(eo::dt_selectors (as leaf (Tree Int))) == eo::List::nil
```

In particular, the constructors of a *fully* instantiated parameteric datatype are such that its ambiguous constructors are annotated in the return value, and its unambiguous constructors are included as-is.
The selectors of a constructor (which are never ambiguous) are returned independently of whether the constructor is annotated.

> __Note:__ Note that `eo::dt_constructors` does not evaluate on parametric types that are partially applied, e.g. `(eo::dt_constructors (Pair Int))` does not evaluate, where `Pair` expects two type parameters.

## Declaring Proof Rules

The generic syntax for a `declare-rule` command accepted by `ethos` is:

```smt
(declare-rule <symbol> (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? <conclusion> <attr>*)
where
<assumption>   ::= :assumption <term>
<premises>     ::= :premises (<term>*) | :premise-list <term> <term>
<arguments>    ::= :args (<term>*)
<reqs>         ::= :requires ((<term> <term>)*)
<conclusion>   ::= :conclusion <term> | :conclusion-explicit <term>
```

A proof rule begins by defining a list of free parameters, followed by 4 optional fields and a conclusion term.
These fields include:

- `<premises>`, denoting the premise patterns of the proof rule. This is, either, a list of formulas (via `:premises`) or the specification of a list of premises (via `:premise-list`), which will be described in detail later.
- `<arguments>`, denoting argument patterns provided to a proof rule.
- `<reqs>`, denoting a list of pairs of terms.

Proof rules with assumptions `<assumption>` are used in proofs with local scopes and will be discussed in detail later.

Proof rules may be marked with attributes at the end of their definition. 
The only attribute of this form that is currently supported is `:sorry`, which indicates that the proof rule does not have a formal justification.
This, in turn, impacts the response of Ethos, as described in [responses](#responses).

At a high level, an application of a proof rule is given a concrete list of (premise) proofs, and a concrete list of (argument) terms.
A proof rule checks if a substitution `S` can be found such that:

- The formulas proved by the premise proofs match the provided premise patterns under substitution `S`,
- The argument terms match the provided argument patterns under substitution `S`,
- The requirements are _satisfied_ under substitution `S`, namely, each pair of terms in the requirements list evaluates pairwise to the same term.
If these criteria are met, then the proof rule proves the result of applying `S` to the conclusion term.

A proof rule is only well defined if the free parameters of the requirements and conclusion term are also contained in the arguments and premises.

> __Note:__ Internally, proofs can be seen as terms whose type is given by a distinguished `Proof` type. In particular, `Proof` is a type whose kind is `(-> Bool Type)`, where the argument of this type is the formula that is proven. For example, `(Proof (> x 0))` is the proof that `x` is greater than zero. By design, the user cannot declare terms involving type `Proof`. Instead, proofs can only be constructed via the commands `assume` and `step` as we describe in [proofs](#proofs).

### Example rule: Reflexivity of equality

```smt
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
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

```smt
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-rule symm ((T Type) (t T) (s T))
    :premises ((= t s))
    :conclusion (= s t)
)
```

This rule specifies symmetry of equality. This rule takes as premise an equality `(= t s)` and no arguments.
In detail, an application of this proof rule for premise proof `(= a b)` for concrete terms `a,b` will compute the substitution `{ t -> a, s -> b }` and apply it to the conclusion term to obtain `(= b a)`.

### Requirements

A list of requirements can be given to a proof rule.

```smt
(declare-const Int Type)
(declare-consts <numeral> Int)
(declare-const >= (-> Int Int Bool))
(declare-rule leq-contra ((x Int))
    :premise ((>= x 0))
    :requires (((eo::is_neg x) true))
    :conclusion false)
```

This rule expects an arithmetic inequality.
It requires that the left hand side of this inequality `x` is a negative numeral, which is checked via the requirement `:requires (((eo::is_neg x) true))`.
The above requires annotation is equivalent to wrapping the conclusion in an `eo::requires` term (for details, see [computation](#computation)).
In particular, the above is equivalent to:

```smt
(declare-rule leq-contra ((x Int))
    :premise ((>= x 0))
    :conclusion (eo::requires (eo::is_neg x) true false))
```

### Premise lists

A rule can take an arbitrary number of premises via the syntax `:premise-list <term><term>`. For example:

```smt
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
(declare-rule and-intro ((F Bool))
    :premise-list F and
    :conclusion F)
```

This syntax specifies that the number of premises that are provided to this rule are arbitrary.
When applying this rule, the formulas proven to this rule (say `F1 ... Fn`) will be collected and constructed as a single formula via the provided operator (`and`), and subsequently matched against the premise pattern `F`.
In particular, in this case `F` is bound to `(and F1 ... Fn)`.
The conclusion of the rule returns `F` itself.

Note that the type of functions provided as the second argument of `:premise-list` should be operators that are marked to take an arbitrary number of arguments, that is those marked e.g. with `:right-assoc-nil` or `:chainable`.

<a name="proofs"></a>

### Explicit Conclusions

Rules can be specified to pattern match on the provided conclusion as input.
This is useful if the proof rule is written in the style where an arbitrary conclusion can be provided by user, and is checked to see if it is a valid possible conclusion of the rule.
For example:

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil true)
(declare-const not (-> Bool Bool))

(declare-rule split ((F Bool))
  :conclusion-explicit (or F (not F))
)
(step @p0 (or true (not true)) :rule split)
```

In the above rule definition, a proof rule `split` is given which expects a conclusion of the form `(or F (not F))` to be provided.
A step invoking this rule is only valid if the provided conclusion of that step matches this pattern.
Further requirements can be added, e.g. checking that `F` satisfies some side condition,
where it is assumed that `F` is bound to the term found when matching the conclusion of the rule.
Any step not providing a conclusion as the second argument to the step command will result in a proof checking failure.

## Writing Proofs

The Eunoia language provides the commands `assume` and `step` for defining proofs. Their syntax is given by:

```smt
(assume <symbol> <term>)
(step <symbol> <term>? :rule <symbol> <premises>? <arguments>?)
where
<premises>     ::= :premises (<term>*)
<arguments>    ::= :args (<term>*)
```

### Example proof: symmetry of equality

```smt
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-rule symm ((T Type) (t T) (s T))
    :premises ((= t s))
    :conclusion (= s t)
)
(declare-const Int Type)
(declare-const a Int)
(declare-const b Int)
(assume @p0 (= a b))
(step @p1 (= b a) :rule symm :premises (@p0))
```

## Proofs with local assumptions

The Eunoia language includes commands `assume-push` and `step-pop` with the same syntax as `assume` and `step` respectively.
However, the former can be seen as introducing a local assumption that is consumed by the latter.
We give an example of this, below.

```smt
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

```smt
...
(assume-push @p0 true)
(assume-push @p1 false)
(step @p2 true :rule contra :premises (@p1) :args (true))
(step-pop @p3 (=> false true) :rule implies-intro :premises (@p2))
(step-pop @p4 (=> true (=> false true)) :rule implies-intro :premises (@p3))
```

## Programs

Ethos supports a `program` command for defining recursive programs.
In particular, in Ethos, a program is an ordered list of rewrite rules.
The syntax for this command is as follows.

```smt
(program <symbol> (<typed-param>*) :signature (<type>+) <type> ((<term> <term>)+))
```

This command declares a program named `<symbol>`.
The provided type parameters are implicit and are used to define the program's type signature and body.

The type of the program is given immediately after the parameter list, provided as a list of argument types and a return type.
The semantics of the program is given by a non-empty list of pairs of terms, which we call its _body_.
For program `f`, this list is expected to have the form `(((f t11 ... t1n) r1) ... ((f tm1 ... tmn) rm))`
where `t11...t1n, ..., tm1...tmn` do not contain computational operators.
A (ground) term `(f s1 ... sn)` evaluates by finding the first term from the first component of a pair from `f`'s body that matches it for a substitution `S`, and returns the result of applying `S` to the second component of said pair.
If no such term can be found, then the application does not evaluate.

> __Note:__ Terms in program bodies are not statically type checked. Evaluating a program may introduce non-well-typed terms if the program body is malformed.

> __Note:__ For each case `((f ti1 ... tin) ri)` in the program body, the free parameters in `ri` are required to be a subset of the free parameters in `(f ti1 ... tin)`. Otherwise, an error is thrown.

> __Note:__ If a case is provided `(si ri)` in the definition of program `f` where `si` is not an application of `f`, an error is thrown.
Furthermore, if `si` contains any computational operators (i.e. those with `eo::` prefix), then an error is thrown.

> __Note:__ Programs are *not* invoked on terms that fail to evaluate. For example, if a function `f : Int -> Int` is applied to `(eo::add "A" "B")`, we return `(f (eo::add "A" "B"))`.

> __Note:__ Programs are *not* invoked when applied to other programs in this version of Ethos. For example, the application of a program `f : (Int -> Int) -> Int` to another user defined program `g : Int -> Int` will be unevaluated, i.e. `(f g)`. Similarly, programs are not invoked when applied to builtin operators `eo::` and oracle functions. In contrast, `f` is invoked when `g` is an ordinary term e.g. one defined by `declare-const`.

### Example: Finding a child in an `or` term

The following program (recursively) computes whether a formula `l` is contained as the direct child of an application of `or`:

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(program contains
    ((l Bool) (x Bool) (xs Bool :list))
    :signature (Bool Bool) Bool
    (
        ((contains false l)     false)
        ((contains (or l xs) l) true)
        ((contains (or x xs) l) (contains xs l))
    )
)
```

First, we declare the parameters `l, x, xs`, each of type `Bool`.
These parameters are used for defining the body of the program, but do _not_ necessarily coincide with the expected arguments to the program.
We then declare the type of the program `(Bool Bool) Bool`, i.e. the type of `contains` is a function expecting two Booleans and returning a Boolean.
The body of the program is then given in three cases.
First, terms of the form `(contains false l)` evaluate to `false`, that is, we failed to find `l` in the first argument.
Second, terms of the form `(contains (or l xs) l)` evaluate to `true`, that is we found `l` in the first position of the first argument.
Otherwise, terms of the form `(contains (or x xs) l)` evaluate in one step to `(contains xs l)`, in other words, we make a recursive call to find `l` in the tail of the list `xs`.

In this example, since `xs` was marked with `:list`, the terms `(or l xs)` and `(or x xs)` are desugared to terms where `xs` is matched with the tail of the input.
The next two examples show variants where an incorrect definition of this program is defined.

> __Note:__ As mentioned in [list-computation](#list-computation), Eunoia has dedicated support for operators over lists.
For the definition of `contains` in the above example, the term `(contains c l)` is equivalent to `(eo::not (eo::is_neg (eo::list_find or c l)))`.
Computing the latter is significantly faster in practice in Ethos.

### Example: Finding a child in an `or` term (incorrect version)

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(program contains
    ((l Bool) (x Bool) (xs Bool))
    :signature (Bool Bool) Bool
    (
        ((contains false l)     false)
        ((contains (or l xs) l) true)
        ((contains (or x xs) l) (contains xs l))
    )
)
```

In this variant, `xs` was not marked with `:list`.
Thus, `(or l xs)` and `(or x xs)` are desugared to `(or l (or xs false))` and `(or x (or xs false))` respectively.
In other words, these terms will match `or` terms with _exactly_ two children, for example `(contains (or a b) a)` will still evaluate to `true`.
However, `(contains (or a b c) a)` does not evaluate in this example.

### Example: Finding a child in an `or` term (incorrect version 2)

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(program contains
    ((l Bool) (x Bool :list) (xs Bool :list))
    :signature (Bool Bool) Bool
    (
        ((contains false l)     false)
        ((contains (or l xs) l) true)
        ((contains (or x xs) l) (contains xs l))
    )
)
```

In this variant, both `xs` and `x` were marked with `:list`.
Ethos will reject this definition since it implies that a computational operator appears in a pattern for matching.
In particular, the term `(or x xs)` is equivalent to `(eo::list_concat or x xs)` after desugaring.
Thus, the third case of the program, `(contains (eo::list_concat or x xs) l)`, is not a legal pattern.

### Example: Substitution

```smt
(program substitute
  ((T Type) (U Type) (S Type) (x S) (y S) (f (-> T U)) (a T) (z U))
  :signature (S S U) U
  (
  ((substitute x y x)     y)
  ((substitute x y (f a)) (_ (substitute x y f) (substitute x y a)))
  ((substitute x y z)     z)
  )
)
```

The term `(substitute x y t)` replaces all occurrences of `x` by `y` in `t`.
Note that this side condition is fully general and does not depend on the shape of terms in `t`.
In detail, recall that Ethos treats all function applications as curried (unary) applications.
In particular, this implies that `(f a)` matches any application term, since both `f` and `a` are parameters.
Thus, the side condition is written in three cases: either `t` is `x` in which case we return `y`, `t` is a function application in which case we recurse, or otherwise `t` is a constant not equal to `x` and we return itself.

This method will not replace subterms inside of opaque arguments (see [opaque](#opaque)).
In particular, a term such as `(@array_diff A B)` will remain unchanged for a substitution e.g. replacing `A` with `B`, since `(@array_diff A B)` is not a function application.
Hence when `t` is `(@array_diff A B)`, we fall into the third case of the method above for any call to `substitute` where `x` is not `(@array_diff A B)` itself.

Alternatively, the following version of substitution `substitute-o` pattern matches on applications of `@array_diff` explicitly.
Calling it with arguments `A`, `B`, and `(@array_diff A B)` would return `(@array_diff B B)`.

```smt
(program substitute-o
  ((T Type) (U Type) (S Type) (x S) (y S) (a (Array T U)) (b (Array T U)) (z U))
  :signature (S S U) U
  (
  ((substitute-o x y x)                 y)
  ((substitute-o x y (f a))             (_ (substitute-o x y f) (substitute-o x y a)))
  ((substitute-o x y (@array_diff a b)) (@array_diff (substitute-o x y a) (substitute-o x y b)))
  ((substitute-o x y z)                 z)
  )
)
```

### Example: Term evaluator

```smt
(declare-const Int Type)
(declare-consts <numeral> Int)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-const + (-> Int Int Int))
(declare-const - (-> Int Int Int))
(declare-const < (-> Int Int Bool))
(declare-const <= (-> Int Int Bool))

(program run_evaluate ((T Type) (U Type) (S Type) (a T) (b U) (z S))
    :signature (S) S
    (
      ((run_evaluate (= a b))  (eo::is_eq (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (< a b))  (eo::is_neg (run_evaluate (- a b))))
      ((run_evaluate (<= a b)) (let ((x (run_evaluate (- a b))))
                                 (eo::or (eo::is_neg x) (eo::is_eq x 0))))
      ((run_evaluate (+ a b))  (eo::add (run_evaluate a) (run_evaluate b)))
      ((run_evaluate (- a b))  (eo::add (run_evaluate a) (eo::neg (run_evaluate b))))
      ((run_evaluate z)        z)
    )
)
```

The above example recursively evaluates arithmetic terms and predicates according to their intended semantics.

### Example: A computational type rule

```smt
(declare-const Int Type)
(declare-const Real Type)
(program arith.typeunion ()
    :signature (Type Type) Type
    (
      ((arith.typeunion Int Int) Int)
      ((arith.typeunion Int Real) Real)
      ((arith.typeunion Real Int) Real)
      ((arith.typeunion Real Real) Real)
    )
)
(declare-parameterized-const + ((T Type :implicit) (U Type :implicit))
  (-> T U (arith.typeunion T U)))
```

In the above example, a side condition is being used to define the type rule for the function `+`.
In particular, `arith.typeunion` is a program taking two types and returning a type, which is `Real` if either argument is `Real` or `Int` otherwise.
The return type of `+` invokes this side condition, which conceptually is implementing a policy for subtyping over arithmetic types.

### Example: Conversion to DIMACS

```smt
(declare-const String Type)
(declare-consts <string> String)
(declare-const not (-> Bool Bool))
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)

(program to_drat_lit ((l Bool))
  :signature (Bool) Int
  (
    ((to_drat_lit (not l))  (eo::neg (eo::hash l)))
    ((to_drat_lit l)        (eo::hash l))
  )
)
(program to_drat_clause ((l Bool) (C Bool :list))
  :signature (Bool) String
  (
    ((to_drat_clause false)    "0")
    ((to_drat_clause (or l C)) (eo::concat (eo::to_str (to_drat_lit l)) " " (to_drat_clause C)))
    ((to_drat_clause l)        (eo::concat (eo::to_str (to_drat_lit l)) " 0"))
  )
)
(program to_dimacs ((C Bool) (F Bool :list))
  :signature (Bool) String
  (
    ((to_dimacs true)       "")
    ((to_dimacs (and C F))  (eo::concat (to_drat_clause C) " " (to_dimacs F)))
  )
)
```

The above program `to_dimacs` converts an SMT formula into DIMACS form, where `eo::hash` is used to assign atoms to integer identifiers.

### Dependently-Typed Programs

In Eunoia, a program can be given dependent types.
The syntax `eo::quote` is used for this purpose, which can specify an input parameter to that function,
and is provided as part of the type signature of the program.

```
(declare-const Int Type)
(declare-consts <numeral> Int)
(declare-const BitVec (-> Int Type))
(declare-consts <binary> (BitVec (eo::len eo::self)))

(declare-const @bv_empty (BitVec 0))

(declare-parameterized-const concat ((n Int :implicit) (m Int :implicit))
  (-> (BitVec n) (BitVec m) (BitVec (eo::add n m))))

(program repeat_zero ((n Int))
  :signature ((eo::quote n)) (BitVec n)
  (
    ((repeat_zero 0) @bv_empty)
    ((repeat_zero n) (eo::requires (eo::is_neg n) false
                        (concat #b0 (repeat_zero (eo::add n -1)))))
  )
)

(define foo () (repeat_zero 7) :type (BitVec 7))
```

In the above example, we define a parametric bit-vector type and the operator `concat`,
which concatenates two bit-vectors and whose type is the sum of its arguments.
We then define a recursive program `repeat_zero` that concatenates the bit-vector value `#b0`
`n` times, where `n` is its argument.
This program returns a bit-vector of size `n`.
Its specified type uses `eo::quote` to give a name to the argument of this program,
allowing its return type to refer to that argument.

> __Note:__ The argument of `eo::quote` must be a parameter introduced in the parameter list declared at the beginning of the program command.

Note that arguments that use the annotation `eo::quote` can be freely mixed with other type arguments.
For example, the above program could be generalized to concatentate an arbitrary BitVec term `n` times:

```
(program repeat_term ((m Int) (n Int) (x (BitVec m))
  :signature ((BitVec m) (eo::quote n)) (BitVec (eo::mul m n))
  (
    ((repeat_term x 0) @bv_empty)
    ((repeat_term x n) (eo::requires (eo::is_neg n) false
                         (concat x (repeat_term (eo::add n -1)))))
  )
)

(declare-const a (BitVec 5))
(define foo2 () (repeat_term a 7) :type (BitVec 35))
```

### Example: Proof rule for symmetry of (dis)equality

```smt
(declare-const Int Type)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-const not (-> Bool Bool))

(program mk_symm ((T Type) (t1 T) (t2 T))
  :signature (Bool) Bool
  (
    ((mk_symm (= t1 t2))       (= t2 t1))
    ((mk_symm (not (= t1 t2))) (not (= t2 t1)))
  )
)

(declare-rule symm ((F Bool))
    :premises (F)
    :conclusion (mk_symm F)
)
```

The above rule performs symmetry on equality or disequality.
It matches the given premise `F` with either `(= t1 t2)` or `(not (= t1 t2))` and flips the terms on the sides of the (dis)equality.

### Example: Proof rule for transitivity of equality with a premise list

```smt
(declare-const Int Type)
(declare-parameterized-const = ((T Type :implicit)) (-> T T Bool))
(declare-const and (-> Bool Bool Bool) :left-assoc)

(program mk_trans ((t1 Int) (t2 Int) (t3 Int) (t4 Int) (tail Bool :list))
    :signature (Int Int Bool) Bool
    (
        ((mk_trans t1 t2 (and (= t3 t4) tail)) (eo::requires t2 t3 (mk_trans t1 t4 tail)))
        ((mk_trans t1 t2 true)                 (= t1 t2))
    )
)

(declare-rule trans ((t1 Int) (t2 Int) (tail Bool :list))
    :premise-list (and (= t1 t2) tail) and
    :conclusion (mk_trans t1 t2 tail)
)
```

For simplicity, the rule is given only for equalities of the integer sort, although this rule can be generalized.
The proof rule `trans` first packages an arbitrary number of premises, constructs a conjunction of these premises, which to bound to `E` and passed to the match term in the conclusion.
The recursive calls in the side condition `mk_trans` accumulate the endpoints of an equality chain and ensure via `eo::requires` that further equalities extend the left hand side of this chain.

## Including and referencing files

Ethos supports the following commands for file inclusion:

- `(include <string>)`, which includes the file indicated by the given string. The path to the file is taken relative to the directory of the file that includes it.
- `(reference <string> <symbol>?)`, which similar to `include` includes the file indicated by the given string, and furthermore marks that file as being the _reference input_ for the current run of the checker (see below). The optional symbol can refer to a normalization routine (see below).

Additionally, files may be included or referenced on the command line with the options `--include=X` and `--reference=X` respectively.

### Validation Proofs via Reference Inputs

When Ethos encounters a command of the form `(reference <string>)`, the checker enables a further set of checks that ensures that all assumptions in proofs correspond to assertions from the file referenced by the given string.

In particular, when the command `(reference "file.smt2")` is read, Ethos will parse `file.smt2`.
The definitions and declaration commands in this file will be treated as normal, that is, they will populate the symbol table of Ethos as they normally would if they were to appear in an `*.eo` input.
The commands of the form `(assert F)` will add `F` to a set of formulas we will refer to as the _reference assertions_.
Other commands in `file.smt2` (e.g. `set-logic`, `set-option`, and so on) will be ignored.

If ethos has read a reference file, then for each command of the form `(assume <symbol> G)`, ethos will check whether `G` occurs in the set of parsed reference assertions.
If it does not, then an error is thrown indicating that the proof is assuming a formula that is not a part of the original input.

> __Note:__ Only one reference command can be executed for each run of ethos.

> __Note:__ Incremental `*.smt2` inputs are not supported as reference files in the current version of ethos.

### Validation up to Normalization

Since the validation is relying on the fact that ethos can faithfully parse the original *.smt2 file, validation will only succeed if the signatures used by Ethos exactly match the syntax for terms in the *.smt2 file.
Minor changes in how terms are represented will lead to mismatches.
For this reason, ethos additionally supports providing an optional normalization routine via `(reference <string> <term>)`, which includes the file indicated by the given string and specifies all assumptions must match an assertion after running the provided normalization function.

For example:

```smt
(declare-const Int Type)
(declare-const Real Type)
(declare-const / (-> Int Int Real))
(program normalize ((T Type) (S Type) (f (-> S T)) (x S) (a Int) (b Int))
   :signature (T) T
   (
     ((normalize (/ a b)) (eo::qdiv a b))
     ((normalize (f x))   (_ (normalize f) (normalize x)))
     ((normalize y)       y)
   )
)
(reference "file.smt2" normalize)
```

Here, `normalize` is introduced as a program which recursively replaces all occurrences of division (over integer constants) with the resulting rational constant.
This method can be used for handling solvers that interpret constant division as the construction of a rational constant.
The above program will be invoked on all formulas occuring in `assert` commands in `"file.smt2"` and subsequently formulas in `assume` commands.

<a name="responses"></a>

## Checker Response

After successfully parsing an input file with no errors, Ethos will respond with one of two possibilities:

- `incomplete` if it parsed any `step` or `step-pop` application that referenced a proof rule that was marked with the attribute `:sorry`, or
- `correct` otherwise.

Note, however, that Ethos does not impose any requirements on _what_ was proven in the proof.
The user is responsible for ensure that e.g. the proof contains a step with a desired conclusion (e.g. `false`).

## Appendix

### Command line options of ethos

The Ethos command line interface can be invoked by `ethos <option>* <file>` where `<option>` is one of the following:

- `--help`: displays a help message.
- `--include=X`: includes the file specified by `X`.
- `--no-print-dag`: do not dagify the output of terms in error messages and trace messages.
- `--no-rule-sym-table`: do not use a separate symbol table for proof rules and declared terms.
- `--reference=X`: includes the file specified by `X` as a reference file.
- `--show-config`: displays the build information for the given binary.
- `--stats`: enables detailed statistics.
- `--stats-all`: enables all available statistics, including program invocations.
- `--stats-compact`: print statistics in a compact format.
- `-t <tag>`: enables the given trace tag (for debugging).
- `-v`: verbose mode, enable all standard trace messages.

The following options impact how proof files and reference files are parsed only (for details on classifications of files, see [full-syntax](#full-syntax)).
They do not impact how signature files (*.eo) are parsed:

- `--normalize-num`: treat numeral literals as syntax sugar for (integral) rational literals.
- `--no-normalize-dec`: do not treat decimal literals as syntax sugar for rational literals.
- `--no-normalize-hex`: do not treat hexadecimal literals as syntax sugar for binary literals.
- `--no-parse-let`: do not treat `let` as a builtin symbol for specifying a macro.

Most of the above options can also be set via `set-option` commands within proofs or Eunoia scripts.
For example, the command `(set-option normalize-num true)` tells Ethos to normalize numerals always.
Further note that option names in this interface should exclude `no-`, which is equivalent to setting the value of the option to false.
As another example, `(set-option normalize-dec false)` is equivalent to the command line option `--no-normalize-dec`.

<a name="full-syntax"></a>

## Full syntax for Eunoia commands

Below defines the syntax accepted by the Ethos parser.

We distinguish three kinds of file inputs:

- _Proof files_ are files that are given via command line option that do _not_ have extension `*.eo`.
Their expected syntax is `<eo-command>*`.
- _Reference files_ are files included via the `reference` command.
Their expected syntax is `<smtlib2-command>*`.
- _Signature files_ are files that given via command line option that have extension `*.eo`, or those that are included via the command `include`. Like proof files, their expected syntax is `<eo-command>*`.

As mentioned, the first two kinds of file inputs take into account options concerning the normalization of terms (e.g. `--normalize-num`), while signature files do not.
When streaming input to Ethos, we assume the input is being given for a proof file.

```smt
;;;
<eo-command> ::=
    (assume <symbol> <term>) |
    (assume-push <symbol> <term>) |
    (declare-consts <lit-category> <type>) |
    (declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*) |
    (declare-rule <symbol> (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? :conclusion <term> <attr>*) |
    (define <symbol> (<typed-param>*) <term> <attr>*) |
    (include <string>) |
    (program <symbol> (<typed-param>*) :signature (<type>+) <type> ((<term> <term>)+)) |
    (reference <string> <symbol>?) |
    (step <symbol> <term>? :rule <symbol> <simple-premises>? <arguments>?) |
    (step-pop <symbol> <term>? :rule <symbol> <simple-premises>? <arguments>?) |
    <common-command>

;;;
<common-command> ::=
    (declare-const <symbol> <type> <attr>*)
    (declare-datatype <symbol> <datatype-dec>) |
    (declare-datatypes (<sort-dec>^n) (<datatype-dec>^n)) |
    (echo <string>?) |
    (exit) |
    (reset) |
    (set-option <attr>)

;;;
<smtlib2-command> ::=
    (assert <term>) |
    (check-sat) |
    (check-sat-assuming (<term>*)) |
    (declare-fun <symbol> (<type>*) <type> <attr>*) |
    (declare-sort <symbol> <numeral>) |
    (define-const <symbol> <term>) |
    (define-fun <symbol> (<typed-param>*) <type> <term>) |
    (define-sort <symbol> (<symbol>*) <type>) |
    (set-info <attr>) |
    (set-logic <symbol>) |
    <common-command>

;;;
<keyword>       ::= :<symbol>
<attr>          ::= <keyword> <term>?
<term>          ::= <symbol> | (<symbol> <term>+) | (! <term> <attr>+)
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
<conclusion>      ::= :conclusion <term> | :conclusion-explicit <term>

```

### Derived Definitions of Evaluation Operators
<a name="derived-ops"></a>

We provide a signature that give an alternative definition
of certain builtin operators that can be expressed as standard Eunoia programs,
or based on other operators.
We provide this as a parsable Eunoia file, which is part of our
regression tests (see <https://github.com/cvc5/ethos/tree/main/tests/eo-definitions.eo>).

In this signature, we use the convention that each `eo::X` definition is given a corresponding
definition `$eo_X` in the following signature.
Including this signature and modifying a Eunoia
file to use `$eo_` instead of `eo::` should
have no impact on behavior (apart from performance), unless otherwise noted.

The signature above provides definitions of Eunoia list operators in terms
of standard Eunoia programs or definitions.
It is possible to define programs for *all* list operators with the exception
of `eo::nil`.
In particular, the behavior of `eo::nil` is dynamically modified based on the
declared constants. We provide instructions
for how to construct the definition of `$eo_nil` for a fixed signature.

We assume the definition of `$eo_nil` has the following form:

```
; program: $eo_nil
; implements: eo::nil
(program $eo_nil ((T Type) (U Type) (V Type) (W Type))
  :signature ((-> T U V) (eo::quote W)) W
  (
  ; ... Cases for each associative-nil operator, see description below.
  )
)
```

For each declare-const or declare-parameterized-const `f` whose return type is `T`
declared in the signature that is marked `:right-assoc-nil nil` or `:left-assoc-nil nil`,
we add the case`(($eo_nil f T) nil)` to the definition of `$eo_nil` above.
For example, given:
```
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
```
We add the case `(($eo_nil or Bool) false)` to `$eo_nil` above.

> __Note:__ In our formulation, we assume that the case `(($eo_nil eo_List_cons eo_List) eo_List_nil)`
for our (redefinition) of the builtin Eunoia list is included.

In the definition of `$eo_nil`, notice that
it is necessary to include the type as part of the case to support functions with
non-ground nil terminators, which requiring instantiating the free parameters
of `T`. For example, given:
```
(declare-parameterized-const bvor ((m Int :implicit))
  (-> (BitVec m) (BitVec m) (BitVec m)) :right-assoc-nil (eo::to_bin 0 m))
```
We add the case `(($eo_nil bvor (BitVec m))  (eo::to_bin 0 m))` to `$eo_nil` above.
Providing a concrete type, e.g. `(BitVec 4)` will ensure `m` is bound to `4`
and hence `($eo_nil bvor (BitVec 4))` evaluates to `(eo::to_bin 0 4)`, which is
`#b0000`.

All other list operators can be defined as ordinary Eunoia programs or definitions.

### Proofs as terms

This section overviews the semantics of proofs in the Eunoia language.
Proof checking can be seen as a special instance of type checking terms involving the `Proof` and `Quote` types.
The type system of Eunoia can be summarized as follows, where `t : S` are assumed axioms for all atomic terms `t` of type `S`:

```smt
f : (-> (Quote u) S)  t : T
---------------------------- if u * sigma = t
(f t) : S * sigma


f : (-> U S)  t : T
------------------- if U * sigma = T
(f t) : S * sigma

for all other (non-Quote) types U.
```

Note that Ethos additionally requires that all well-typed terms have a type that is either non-ground, or is fully reduced, i.e. contains no irreducible applications of programs or evaluation operators.

The command:

```smt
(declare-rule s ((v1 T1) ... (vi Ti)) 
    :premises (p1 ... pn) 
    :args (t1 ... tm) 
    :requires ((r1 s1) ... (rk sk)) 
    :conclusion t)
```

can be seen as syntax sugar for:

```smt
(declare-parameterized-const s ((v1 T1 :implicit) ... (vi Ti :implicit))
    (-> (Proof p1) ... (Proof pn)
        (Quote t1) ... (Quote tm)
        (eo::requires r1 s1 ... (eo::requires rk sk
            (Proof t)))))
```

The command:

```smt
(assume s f)
```

can be seen as syntax sugar for:

```smt
(declare-const s (Proof f))
```

The command:

```smt
(step s f :rule r :premises (p1 ... pn) :args (t1 ... tm))
```

can be seen as syntax sugar for:

```smt
(define s () (r p1 ... pn t1 ... tm) :type (Proof f))
```

If no conlusion is provided, then the type attribute is not specified.
Notice this is only the case if the declaration of `r` does not involve `:assumption` or `:premise-list`.
