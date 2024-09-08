# The Ethos user manual

This is the user manual for the Ethos, an efficient and extensible tool for checking proofs of Satisfiability Modulo Theories (SMT) solvers.

## Building the Ethos executable

The source code for Ethos is available at <https://github.com/cvc5/ethos>.
To build ethos, run:

```shell
mkdir build
cd build
cmake ..
```

The `ethos` binary will be available in `build/src/`.

### Debug build

By default, the above will be a production build of `ethos`. To build a debug version of `ethos`, that is significantly slower but has assertions and trace messages enabled, run:

```shell
mkdir build -DCMAKE_BUILD_TYPE=Debug
cd build
cmake ..
```

The `ethos` binary will be available in `build/src/`.

## Command line interface

Ethos can be run from the command line via:

```shell
ethos <option>* <file>
```

The set of available options `<option>` are given in the appendix. Note the command line interface of `ethos` expects exactly one file (which itself may reference other files via the `include` command as we will see later). The file and options can appear in any order.

The Ethos will either emit an error message indicating:

- the kind of failure (type checking, proof checking, lexer error),
- the line and column of the failure,

or will print a [successful response](#responses) when it finished parsing all commands in the file or encounters and `exit` command.
Further output can be given by user-provided `echo` commands.

### Streaming input to the Ethos

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
- A command, `declare-oracle-fun`, for defining external, user-provided oracles, that is, functions whose semantics are given by external binaries. Oracles can be used, e.g., for modular proof checking.
- Commands for file inclusion (`include`) and referencing (`reference`). The latter command can be used to specify the name of an `*.smt2` input file that the proof is associated with.

In the following sections, we describe these features in more detail. A full syntax for the commands is given at the end of this document.

### Declaring theory signatures

In Eunoia, as in SMT-LIB version 3.0, a common BNF is used to specify _terms_ (expressions denoting values), _types_ (expressions denoting sets of values) and _kinds_ (expressions denoting sets of types).
In this document, unless specified otherwise, we will use _term_ more generally to refer to a value term, a type, or a kind.
Terms are composed of applications, built-in operators of the language (e.g., for performing computations, see [computation](#computation)), literals (see [literals](#literals)), and three kinds of atomic terms (_constants_, _variables_, and _parameters_) which we describe in the following.
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

> __Note:__ The core logic of the Ethos also uses several builtin types (e.g. `Proof` and `Quote`) which define the semantics of proof rules. These types are intentionally to exposed to the Eunoia user. Details on then can be found throughout this document. More details on the core logic of the Ethos will be available in a forthcoming publication.

In the following, we informally use the syntactic categories `<symbol>` to denote an SMT-LIB 3.0 symbol, `<term>` to denote an SMT-LIB term and `<type>` to denote a term whose type is `Type`. The syntactic category `<typed-param>` is defined, BNF-style, as `(<symbol> <type> <attr>*)`. It binds `<symbol>` as a fresh parameter of the given type and attributes (if provided).

The following commands are supported for declaring and defining types and terms. The first set of commands are identical to those in SMT-LIB version 3.0:

- `(declare-const <symbol> <type> <attr>*)` declares a constant named `<symbol>` whose type is `<type>`. Can be given an optional list of attributes (see [attributes](#attributes)).
<!-- Moved here because it is present in SMT-LIB 3 -->

- `(declare-consts <lit-category> <type>)` declares the class of symbols denoted by the literal category to have the given type.

- `(declare-type <symbol> (<type>*))` declares a new type constructor named `<symbol>` whose kind is `Type` if `<type>*` is empty. If `<type>*` is `<type_1> ... <type_n>`, then kind of `<symbol>` is `(-> <type_1> ... <type_n> Type)`.
  This is a derived command as it is a shorthand for
  `(declare-const <symbol> Type)` if `<type>*` is empty, and for
  `(declare-const <symbol> (-> <type>* Type))` otherwise.

<!--CT Do we really need `define-type`? -->
- `(define-type <symbol> (<type>*) <type>)` defines `<symbol>` to be a lambda term whose type is given by the argument and return types.
- `(declare-datatype <symbol> <datatype-dec>)` defines a datatype `<symbol>`, along with its associated constructors, selectors, discriminators and updaters.

- `(declare-datatypes (<sort-dec>^n) (<datatype-dec>^n))` defines a list of `n` datatypes for some `n>0`.

- `(exit)` causes the checker to immediately terminate.

- `(reset)` removes all declarations and definitions and resets the global scope. This command is similar in nature to its counterpart in SMT-LIB.

The Eunoia language contains further commands for declaring symbols that are not standard SMT-LIB version 3.0:

- `(define <symbol> (<typed-param>*) <term> <attr>*)`, defines `<symbol>` to be a lambda term whose arguments and body and given by the command, or the body if the argument list is empty. Note that in contrast to the SMT-LIB command `define-fun`, a return type is not provided. The provided attributes may instruct the checker to perform e.g. type checking on the given term see [type checking define](#tcdefine).

- `(declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*)` declares a globally scoped variable named `<symbol>` whose type is `<type>`.

> __Note:__ Variables are internally treated the same as constants by Ethos. However, they are provided as a separate category, e.g., for user signatures that wish to distinguish universally quantified variables from free constants. They also have a relationship with user-defined binders, see [binders](#binders), and can be accessed via the builtin operator `eo::var` (see [computation](#computation)).

> __Note:__ Symbol overloading is supported, see [overloading](#overloading).

#### Example: Basic Declarations

```smt
(declare-type Int ())
(declare-const c Int)
(declare-const f (-> Int Int Int))
(declare-const g (-> Int (-> Int Int)))
(declare-const P (-> Int Bool))
```

Since Ethos does not assume any builtin definitions of SMT-LIB theories, definitions of standard symbols in SMT-LIB theories(such as `Int`, `+`, etc.) must be provided in Eunoia signatures. In the above example, symbol `c` is declared to be a constant (0-ary) symbol of type `Int`. The symbol `f` is a function taking two integers and returning an integer.

Observe that despite the use of different syntax in their declarations, the types of `f` and `g` in the above example are identical as `->` is a right-associative binary type constructor.

> __Note:__ In Eunoia, all functions are unary. In the above example, `(-> Int Int Int)` is internally treated as `(-> Int (-> Int Int))`. Correspondingly, applications of functions are curried, e.g. `(f a b)` is treated as `((f a) b)`, which in turn can be seen as `(_ (_ f a) b)` where `_` denotes higher-order function application.

#### Example: Basic Definitions

```smt
(declare-const not (-> Bool Bool))
(define id ((x Bool)) x)
(define notId ((x Int)) (not (id x)))
```

In the example above, `not` is declared to be a unary function over Booleans. Two defined functions are given, the first being an identity function over Booleans, and the second returning the negation of the first.

Since `define` commands are treated as (hygienic) macro definitions, in this example, `id` is mapped to the lambda term whose SMT-LIB version 3 syntax is `(lambda ((x Bool)) x)`.
Furthermore, `notId` is mapped to the lambda term `(lambda ((x Bool)) (not x))`.
In other words, the following sequence of commands is equivalent to the one above after parsing:

```smt
(declare-const not (-> Bool Bool))
(define id ((x Bool)) x)
(define notId ((x Int)) (not x))
```

#### Example: Polymorphic types

Eunoia supports the declaration of polymorphic types, that is, types depending on other types.

```smt
(declare-type Int ())
(declare-type Array (Type Type))
(declare-const a (Array Int Bool))

(define IntArray ((T Type)) (Array Int T))
(declare-const b (IntArray Bool))
```

In the above example, we declare and integer type constructor of kind `Type` and array type constructor of kind is `(-> Type Type Type)`.

<!-- We should say something about the defines above -->

Note the following declarations generate terms of the same type:

```smt
(declare-type Array_v2 (Type Type))
(declare-const Array_v3 (-> Type Type Type))
```

<a name="literals"></a>

### The :type attribute for definitions

To type check terms, `define` statements can be annotated with `:type <term>`.
This allows the user to eagerly check that a term has a particular type at the place where it is defined.
In particular:

```smt
(declare-const not (-> Bool Bool))
(define notTrue () (not true) :type Bool)
```

This indicates that the checker compare the type it computed for the term `(not true)` and compare it with the specified type `Bool`. An error will be thrown if the two types are not identical.

### The :var and :implicit annotations

The Eunoia language uses the SMT-LIB version 3.0 attributes `:var <symbol>` and `:implicit` in term annotations for naming arguments of functions and specifying they are implicit.

```smt
(declare-type Int ())
(declare-const eq (-> (! Type :var T) T T Bool))
(define P ((x Int) (y Int)) (eq Int x y))
```

The above example declares a predicate symbol `eq` whose first argument is a type, that is given a name `T`. It then expects two terms of type `T` and returns a `Bool`. In the definition of `P`, `eq` is applied to two variables, with type `Int` explicitly provided.

In contrast, the example below declares a predicate `=` where the type of the arguments is implicit (this corresponds to the SMT-LIB standard definition of `=`). In the definition of `P`, the type of the arguments `Int` is not provided.

```smt
(declare-type Int ())
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(define P ((x Int) (y Int)) (= x y))
```

In general, an argument can be made implicit if its value can be inferred from the type of later arguments.

We call `T` in the above definitions a _parameter_. The free parameters of the return type of an expression should be contained in at least one non-implicit argument. In particular, the following declaration is malformed, since the return type of `f` cannot be inferred from its arguments:

```smt
(declare-type Int ())
(declare-const f (-> (! Type :var T :implicit) Int T))
```

> __Note:__ Internally, `(! T :var t)` is syntax sugar for the type `(Quote t)` where `t` is a parameter of type `T` and `Quote` is a distinguished type of kind `(-> (! Type :var U) U Type)`. When type checking applications of functions of type `(-> (Quote t) S)`, the parameter `t` is bound to the argument the function is applied to.

> __Note:__ Internally, `(! T :implicit)` drops `T` from the list of arguments of the function type we are defining.

### The :requires annotation

Arguments to functions can also be annotated with the attribute `:requires (<term> <term>)` to denote a equality condition that is required for applications of the term to type check.

```smt
(declare-type Int ())
(declare-const BitVec (-> (! Int :var w :requires ((eo::is_neg w) false)) Type))
```
The above declares the integer type `Int` and a bitvector type constructor `BitVec` that expects a _non-negative integer_ `w`.
In detail, the first argument of `BitVec` is supposed to be an `Int` value and is named `w` via the `:var` attribute.
The second annotation indicates that the term `(eo::is_neg w)` must evaluate to `false` at type checking type.
Symbol `eo::is_neg` denotes a builtin function that returns `true` if its argument is a negative numeral, and returns false otherwise (for details, see [computation](#computation)).
<!-- This needs discussion, what is the input type of `eo::is_neg`? How can `eo::is_neg` accept a value of a user-defined type `Int` given that it is builtin?  -->

> __Note:__ Internally, `(! T :requires (t s))` is syntax sugar for the type term `(eo::requires t s T)` where `eo::requires` is an operator that evaluates to its third argument if and only if its first two arguments are _computationally_ equivalent (details on this operator are given in [computation](#computation)).
Furthermore, the function type `(-> (eo::requires t s T) S)` is treated as `(-> T (eo::requires t s S))`. Ethos rewrites all types of the former form to the latter.

<a name="opaque"></a>

### The :opaque annotation

The attribute `:opaque` can be used to denote that a distinguished argument to a function.
In particular, functions with opaque arguments intuitively can be considered a _family_ of functions indexed by their opaque arguments.
An example of this annotation is the following:

```smt
(declare-type Array (Type Type))
(declare-const @array_diff
   (-> (! Type :var T :implicit) (! Type :var U :implicit)
   (! (Array T U) :opaque)
   (! (Array T U) :opaque)
   T))

(declare-type Int ())
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
The concatenation of the expected arguments can be passed to the symbol in the order they are given.
For example:

```smt
(declare-type Int ())
(declare-const @purify_fun (-> (! (-> Int Int) :opaque) Int Int))

(declare-const f (-> Int Int))
(declare-const a Int)
(define d () (@purify_fun f a) :type Int)
```

In this example, `@purify_fun` is declared as a function with one opaque argument, and ordinary integer argument, and returns an integer.
Intuitively, this definition is introducing a new function, indexed by a function, that is of type `(-> Int Int)`.
After parsing, the term `(@purify_fun f a)` is a function application whose operator is `(@purify_fun f)` and has a single child `a`.

> __Note:__ Opaque arguments should always be expected before other arguments. Otherwise all applications of the given function will be ill-typed.

<a name="attributes"></a>

### Declarations with attributes

The Eunoia language supports term annotations on declared constants, which for instance allow the user to treat a constant as being variadic, i.e. taking an arbitrary number of arguments. The available annotations for this purpose are:

- `:right-assoc` (resp. `:left-assoc`) denoting that application of the declared binary constant to more than two terms are to be treated as right (resp. left) associative,

- `:right-assoc-nil <term>` (resp. `:left-assoc-nil <term>`) denoting that applications of the declared binary constant to one or more terms are to be treated as right (resp. left) associative, with the given `<term>` used as an additional rightmost (resp. leftmost) argument.

- `:chainable <symbol>` denoting that the arguments of the declared binary constant are chainable using the (binary) operator given by `<symbol>`,

- `:pairwise <symbol>` denoting that the arguments of the declared constant are treated pairwise using the (binary) operator given by `<symbol>`.

- `:binder <symbol>` denoting that the first argument of the declared constant can be provided using a syntax for variable lists whose constructor is the one provided by `<symbol>`.

A declared function can be marked with at most one of the above attributes or an error is thrown.

A parameter may be marked with the following attribute:

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
More generally, a constant declared with the `:right-associative` annotation must have a type of the form `(-> T1 T2 T2)` for some types `T1` and `T2`. Similarly, a constant declared with the `:left-associative` annotation must have a type of the form `(-> T1 T2 T1)`.

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

The type for right and left associative operators with nil terminators is typically `(-> T T T)` for some `T`, where their nil terminator has type `T`. More generally, a constant declared with the `:right-associative-nil` annotation must have a type of the form `(-> T1 T2 T2)` where `T2` is the type of the nil constant, for some types `T1` and `T2`. Similarly, a constant declared with the `:left-associative` annotation must have a type of the form `(-> T1 T2 T1)` where `T1` is the type of the nil constant.

The nil terminator of a right associative operator may involve previously declared symbols in the signature.
For example:

```smt
(declare-type RegLan ())
(declare-const re.all RegLan)
(declare-const re.inter (-> RegLan RegLan RegLan) :right-assoc-nil re.all)
```

This example defines the constant `re.all` (in SMT-LIB, this is the regular expression generating the set of all strings)
and the function `re.inter` (in SMT-LIB, the intersection of regular expressions), where the latter is defined to have a nil terminator
that references the free constant `re.all`.

However, when using `declare-const`, the nil terminator of an associative operator cannot depend on the parameters of the type of that function.
For example, say we wish to declare bitvector or (`bvor` in SMT-LIB), where its nil terminator is bitvector zero for the given bit width.
A possible declaration is the following:

```smt
(declare-const bvor
    (-> (! Int :var m :implicit) (BitVec m) (BitVec m) (BitVec m))
    :right-assoc-nil ???
)
```

The nil terminator of this operator is the bitvector zero whose width is `m`.
However note that `m` is not in scope of the declaration of its nil terminator.
We instead require such declarations to be made with `declare-parameterized-const`, which we will describe later in [param-constants](#param-constants).

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

- If `ti` is marked as `:list` where `1 <= i < n`, then `ti` is prepended to the overall application using a concatenation operation `eo::list_concat`. The semantics of this operator is provided later in [list-computation](#list-computation).

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

#### Chainable

```smt
(declare-type Int ())
(declare-const and (-> Bool Bool Bool) :right-assoc)
(declare-const >= (-> Int Int Bool) :chainable)
(define ((x Int) (y Int) (z Int)) (>= x y z))
(define Q ((x Int) (y Int)) (>= x y))
```

In the above example, `(>= x y z w)` is syntax sugar for `(and (>= x y) (>= y z))`,
whereas the term `(>= x y)` is not impacted by the annotation `:chainable` since it has fewer than 3 children.

Note that the type for chainable operators is typically `(-> T T S)` for some types `T` and `S`,
where the type of its chaining operator is `(-> S S S)`, and that operator has been as variadic via some attribute (e.g. `:right-assoc`).

#### Pairwise

```smt
(declare-type Int ())
(declare-const and (-> Bool Bool Bool) :right-assoc)
(declare-const distinct (-> (! Type :var T :implicit) T T Bool)
 :pairwise and)
(define P ((x Int) (y Int) (z Int)) (distinct x y z))
```

In the above example, `(distinct x y z)` is treated as `(and (distinct x y) (distinct x z) (distinct y z))`.

Note that the type for pairwise operators is typically `(-> T T S)` for some types `T` and `S`,
where the type of its pairwise operator is `(-> S S S)`,
and that operator has been marked as variadic via some attribute.

<a name="binders"></a>

#### Binder

```smt
(declare-type Int ())
(declare-type @List ())
(declare-const @nil @List)
(declare-const @cons (-> (! Type :var T :implicit) T @List @List)
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

Note that if the option `--binder-fresh` is enabled, then when parsing reference files, the variables in binders are always fresh.
This option does not impact how binders are parsed in Eunoia files.

<a name="literals"></a>

### Literal types

The Eunoia language supports associating SMT-LIB version 3.0 syntactic categories with types. In detail, a syntax category is one of the following:

- `<boolean>` denoting the category of _Boolean_ literals `true | false`,
- `<numeral>` denoting the category of (integer) _numerals_ `-?<digit>+` where `<digit>` is `[0-9]`,
- `<decimal>` denoting the category of _decimals_ `-?<digit>+.<digit>+`,
- `<rational>` denoting the category of _rationals_ `-?<digit>+/<digit>+`,
- `<binary>` denoting the category of _binaries_ `#b[0-1]+`,
- `<hexadecimal>` denoting the category of _hexadecimals_ `#x<hex-digit>+` where `<hex-digit>` is `[0-9] | [a-f] | [A-F]`,
- `<string>` denoting the category of _strings_ literals `"<char>*"` <!--CT Added-->where `<char>` consists of the set of UTF-8 characters.

<!--CT Added. -->
We call _literal_ or _value_ any element of the seven syntactic categories above.
We refer to collectively to binaries and hexadecimals as _bit vector values_ and to numerals, decimals and rationals as _arithmetic values_.

<!--CT Added. -->
> __Note:__ Numerals include _negated_ literals such as `-1`, `-43`, and so on. Also, and in contrast to SMT-LIB version 2, rational literals can be specified directly using the syntax `5/11`, `2/4`, `0/1` and so on, and negative values can be provided as single literals, e.g., `-1`, `-10.5`, `-1/3` and so on, instead of terms such as `(- 1)`, `(- 10.5)`, and `(/ (- 1) 3)`.

By default, decimal literals are treated by Ethos as syntax sugar for rational literals.
Similarly, hexadecimal literals are treated as syntax sugar for binary literals.
Rationals are normalized so that, e.g., `2/4` and `1/2` are syntactically equivalent after parsing.
Similarly, decimals are normalized so that, e.g., `1.300` is syntactically equivalent to `1.3` after parsing.
Note this is independent of whether these decimal values are further normalized to rational values.
In other words, by default `1.300` is syntactically equivalent to the rational `13/10`.

String values use the standard escape sequences as specified in SMT-LIB version 2.6, namely `""` within a string literal denotes `"`.
The only other escape sequences are of the form `\u{dn ...d1}` for `1<=n<=5` and `\u d4 d3 d2 d1` for hexadecimal digits `d1...d5` where `d5` is in the range `[0-2]`.

> __Note:__ Numeral, rational and decimal values are implemented by the arbitrary precision arithmetic library GMP. Binary and hexadecimal values are implemented as layer on top of numeral values that tracks a bit width. String values are implemented as a vector of unsigned integers whose maximum value is specified by SMT-LIB version 2.6, namely the character set corresponds to Unicode values 0 to 196607.
> __Note:__ Numeral, rational and decimal values are implemented by the arbitrary precision arithmetic library GMP. Binary and hexadecimal values are implemented as layer on top of numeral values that tracks a bit width. String values are implemented as a vector of unsigned integers whose maximum value is specified by SMT-LIB version 2.6, namely the character set corresponds to Unicode values 0 to 196607.

> __Note:__ Except for `<boolean>`, the literal categories above are not associated to any type by default. The user must decides what type to assign to each of them, with the command `declare-consts`. In contrast, the values of `<boolean>` have the predefined type `Bool`. In other words, `(declare-type Bool ())` and `(declare-consts <boolean> Bool)` are part of the builtin signature assumed by Ethos.

<a name="declare-consts"></a>

#### Declaring classes of literals

The following gives an example of how to define the class of numeral constants.

```smt
(declare-type Int ())
(declare-consts <numeral> Int)
(define P ((x Int)) (> x 7))
```

In the above example, the `declare-consts` command specifies that numerals (`1`, `2`, `3`, and so on) are constants of type `Int`.
The signature can now refer to arbitrary numerals in definitions, e.g. `7` in the definition of `P`.

> __Note:__ Internally, the command above only impacts the type rule assigned to numerals that are parsed. Furthermore, the Ethos internally distinguishes whether a term is a numeral value, independently of its type, for the purposes of computational operators (see [computation](#computation)).

> __Note:__ For specifying literals whose type rule varies based on the content of the constant, the Eunoia language uses a distinguished variable `eo::self` which can be used in `declare-consts` definitions. For an example, see the type rule for SMT-LIB bit-vector constants, described later in [bv-literals](#bv-literals).
> __Note:__ For specifying literals whose type rule varies based on the content of the constant, the Eunoia language uses a distinguished variable `eo::self` which can be used in `declare-consts` definitions. For an example, see the type rule for SMT-LIB bit-vector constants, described later in [bv-literals](#bv-literals).

<a name="computation"></a>

## Computational Operators

The Ethos has builtin support for computations over all syntactic categories of SMT-LIB version 3.0.
We list the operators below, roughly categorized by domain.
<!--CT Added -->
Note that all the operators operate on _terms_, _regardless_ of the user-defined type
assigned to those terms. The behavior of each operator is based only on the syntax of its input terms, not their types.

Some of the operators are overloaded, i.e., they can be applied to multiple syntactic categories, with different behavior for each category.
For example, `eo::add` returns the result of adding two numerals or rationals, but also can be used to add binary values (integers modulo a given bit width).
Similarly, `eo::concat` returns the result of concatenating two string values, but can also concatenate two binary values.
We remark on the semantics in the following.

In the following, we say a term is _ground_ if it contains no parameters as subterms.
A _Boolean value_ is one of the Booleans `true` or `false`.
An _arithmetic value_ is a (possibly negated) numeral, decimal or rational value.
A _bit vector value_ (of bit width n) is a binary or hexadecimal value (of bit width n).
An _$n$-bit numeral_, for $n ≥ 0$ is an numeral between $0$ and $2^n-1$.
Binary values are considered to be in little endian form.

Some of the following operators can be defined in terms of the other operators.
For these operators, we provide the equivalent formulation.
A signature defining these files can be found in [non-core-eval](#non-core-eval).
Note however that the evaluation of these operators is handled by more efficient methods internally in the Ethos checker, that is, they are not treated as syntax sugar internally.

<!--CT Added -->
The semantics of each operator is described in terms of an evaluation function $[ \_ ]$ that takes a term containing applications of the operators and returns a term resulting from this evaluation.
The function $[ \_ ]$ is defined below by specifying how applications of each operator _reduce_ to some (irreducible) term.
With one exception, the if-then-else operator `eo::ite`, term evaluation is bottom up, where the evaluation of an application of the form $(op\ t_1\ \cdots\ t_n)$ is defined in terms of the reduced terms $[t_1]$, ..., $[t_n]$.

<!--CT Added -->
Ideally, the evaluation of an application $(op\ t_1\ \cdots\ t_n)$ results in a term from the set of values (Boolean, arithmetic, etc.).
However, this is not always the case since several operators denote partial functions.
For an input tuple $t_1, \ldots, t_n$ where at least one of the input terms is outside of the definition domain of the operator $op$, the term $(op\ t_1\ \cdots\ t_n)$ reduces only partially,  to $(op\ [t_1] \cdots\ [t_n])$.
In general, we refer to the term $[(op\ t_1\ \cdots\ t_n)]$, whether it is a value or not, as the _result_ of applying $op$ to the terms $t_1, \ldots, t_n$.
<!--CT What happens if a term t contains undeclared symbols? Does that make t only partially reducible or does it raise an error at parse time?-->

<!--CT Added -->
Because of the bottom up evaluation, the specification of the partial operators provided below  assumes for convenience that the provided argument terms $r_1, \ldots, r_n$ __are already reduced__ with respect to $[\_]$, that is, $[r_i] = r_i$
for all $i=1,\ldots,n$.
The specification of each operator $op$ is (intentionally) incomplete. It is understood that in the unspecified cases, if any, $[(op\ r_1\ \cdots\ r_n)] = (op\ [t_1]\ \cdots\ [t_n]) = (op\ r_1\ \cdots\ r_n)$.

### Core operators

In the following, we list the core builtin operators of Ethos.

- `(eo::is_eq r1 r2)`

  evaluates to `true` if `r1` and `r2` are the same term, and `false` if `r1` and `r2` are distinct, ground terms. (Otherwise, it evaluates to itself.)
    More formally, 
    $$[(\textsf{eo::is_eq}\ r_1\ r_2)] =
    \begin{cases}
     \textsf{true} & \text{if } r_1 = r_2 \\
     \textsf{false} & \text{if } r_1, r_2 \text{ are distinct and ground}
    \end{cases}
    $$
   Recalling the note above, the specification of `eo::is_eq` implicitly says that $[(\textsf{eo::is_eq}\ r_1\ r_2)] = (\textsf{eo::is_eq}\ r_1\ r_2)$
   when $r_1$ and $r_2$ are distinct but at least one of them is not ground.

   __Example:__ `(eo::is_eq 5 5)` evaluates to `true`, `(eo::is_eq 4 5)` and `(eo::is_eq true 5)` to `false`, and `(eo::is_eq 5 x)` to `(eo::is_eq 5 x)`.
  <br><br>

- `(eo::ite r t1 t2)`

  evaluates to the value of `t1` if `r` is `true` and to the value of `t2` if `r` is `false`:

    $$
    \begin{array}{rcl}
     [(\textsf{eo::ite}\ \textsf{true}\ t_1\ t_2)] & = & [t_1]  \\
     [(\textsf{eo::ite}\ \textsf{false}\ t_1\ t_2)] & = & [t_2]  \\
    \end{array}
    $$
  Note that int his operator (and this one only) the subterms `t1` and  `t2` are only evaluated if they are the return term.
  <br><br>

- `(eo::requires r1 r2 r3)`

  evaluates to `r3` if `r1` and `r2` are the same term:

    $$[(\textsf{eo::requires}\ r\ r\ r_3)] = r_3$$

   __Example:__ `(eo::requires (eo::is_eq 5 5) true "ok")` evaluates to `"ok"` since `(eo::is_eq 5 5)` evaluates to `true`.
  <br><br>

- `(eo::hash r)`

  If `r` is ground, this evaluates to a numeral that is unique to `r`.
  <br><br>

- `(eo::typeof r)`

  If `r` is ground, this returns the type of `r` (based on the types declared for the constants in `r`).<!--CT what if r contains undeclared symbols?-->
  <br><br>

- `(eo::nameof r)`

  If `r` is a ground constant or variable, this returns the name of `r`, i.e., the string corresponding to the symbol it was declared with.
  
   __Example:__ `(eo::nameof 125)` evaluates to `"125"` and `(eo::nameof x)` evaluates to `"x"`.
   <br><br>

- `(eo::var r1 r2)`

  If `r1` is a string value and `r2` is a ground type, this evaluates to the (unique) variable with name `r1` and type is `r2`.

  >__Note:__ If `(List Int)`, say, is a type, `(eo::nameof (eo::var "x" (List Int)))` evaluates to `"x"` and `(eo::typeof (eo::var "x" (List Int)))` to `(List Int)`.
  <br>

- `(eo::cmp r1 r2)`

  is treated as `(eo::is_neg (eo::add (eo::neg (eo::hash r1)) (eo::hash r2)))`:
  $$[(\textsf{eo::cmp}\ r_1\ r_2)] = [(\textsf{eo::is_neg}\ t)]$$
  where $t$ is $(\textsf{eo::add}\ (\textsf{eo::neg}\ (\textsf{eo::hash}\ r_1))\ (\textsf{eo::hash}\ r_2))$.

   In words, `(eo::cmp r1 r2)` evaluates to `true` (resp., `false`) if `r_1` has a smaller (resp., greater) hash value than `r_2`. Note that this method induces a total order on all values based on the hashing function `eo::hash`.
   <br><br>

- `(eo::is_z r)`

  is treated as `(eo::is_eq (eo::to_z r) r)`:
  $$[(\textsf{eo::is_z}\ r)] =[(\textsf{eo::is_eq}\ (\textsf{eo::to_z}\ r)\ r)]$$

  In words, `(eo::is_z r)` evaluates to `true` (resp., `false`) if `r` is a numeral (resp., is a value other than a numeral).

  __Example:__ `(eo::is_z 125)` and `(eo::is_z -125)` evaluate to `true`, `(eo::is_z 3.2)` to `false` and `(eo::is_z x)` to `(eo::is_z x)`.
  <br><br>

- `(eo::is_q r)`

   is treated as `(eo::is_eq (eo::to_q r) r)`:
  $$[(\textsf{eo::is_q}\ r)] =[(\textsf{eo::is_eq}\ (\textsf{eo::to_q}\ r)\ r)]$$

  In words, `(eo::is_q r)` evaluates to `true` (resp., `false`) if `r` is a rational (resp., is a value other than a rational).

  Note that this evaluates to `false` for decimal literals.
   <br><br>

- `(eo::is_bin r)`

  is treated as `(eo::is_eq (eo::to_bin (eo::len r) r) r)`:
  $$[(\textsf{eo::is_bin}\ t)] =[(\textsf{eo::is_eq}\ (\textsf{eo::to_bin}\ (\textsf{eo::len}\ t)\ t))]$$

  Note this evaluates to `false` for hexadecimal literals.
   <br><br>

- `(eo::is_str r)`

  is treated as `(eo::is_eq (eo::to_str r) r)`:
  $$[(\textsf{eo::is_str}\ r)] =[(\textsf{eo::is_eq}\ (\textsf{eo::to_str}\ r)\ r)]$$

- `(eo::is_bool r)`

  is treated as `(eo::or (eo::is_eq r true) (eo::is_eq r false))`:
  $$[(\textsf{eo::is_bool}\ r)] = (\textsf{eo::or}\ (\textsf{eo::is_eq}\ r\ \textsf{true})\ (\textsf{eo::is_eq}\ r\ \textsf{false}))$$
  <!-- Is this really the case?  
       Does (eo::is_bool x) (where x is a constant/variable) evaluate 
       to (eo::or (eo::is_eq x true) (eo::is_eq x false)) ? 
  -->

- `(eo::is_var r)`

  is treated as `(eo::is_eq (eo::var (eo::nameof r) (eo::typeof r)) r)`:
  $$[(\textsf{eo::is_var}\ r)] =[(\textsf{eo::is_eq}\ (\textsf{eo::var}\ (\textsf{eo::nameof}\ r)\ (\textsf{eo::typeof}\ r))\ r)]$$

### Boolean operators

- `(eo::and r1 r2)`
  - Boolean conjunction if `r1` and `r2` are booleans.
  - Bitwise conjunction if `r1` and `r2` are bit vector values of the same category and bit width.

- `(eo::or r1 r2)`
  - Boolean disjunction if `r1` and `r2` are booleans.
  - Bitwise disjunction if `r1` and `r2` are bit vector values of the same category and bit width.
- `(eo::xor r1 r2)`
  - Boolean exclusive or if `r1` and `r2` are booleans.
  - Bitwise exclusive or if `r1` and `r2` are bit vector values of the same category and bit width.
- `(eo::not r1)`
  - Boolean negation if `r1` is a boolean.
  - Bitwise negation if `r1` is a bit vector value.

### Arithmetic operators

- `(eo::add r1 r2)`
  - If `r1` and `r2` are arithmetic values of the same category, then this evaluates to the sum of `r1` and `r2`.
  - If `r1` and `r2` are bit vector values of the same category and bit width $n$, this evaluates to the binary value corresponding to their (unsigned) sum modulo $n$.

- `(eo::mul r1 r2)`
  - If `r1` and `r2` are arithmetic values of the same category, then this returns the product of `r1` and `r2`.
  - If `r1` and `r2` are bit vector values of the same category and bit width $n$, this returns the binary value corresponding to their (unsigned) product modulo $n$.

- `(eo::neg r1)`
  - If `r1` is a arithmetic value $a$, this returns the arithmetic negation of $a$.
  - If `r1` is a bit vector value, this returns its (signed) arithmetic negation.

- `(eo::qdiv r1 r2)`
  - If `r1` and `r2` are arithmetic values of the same category and `r2` is non-zero, this returns the rational quotient of `r1` divided by `r2`.

- `(eo::zdiv r1 r2)`
  - If `r1` and `r2` are numerals and `r2` is non-zero, this returns the integer quotient (floor) of `r1` divided by `r2`.
  - If `r1` and `r2` are bit vector values of the same syntactic category and bit width n, then this returns their (total, unsigned) quotient, with division by zero returning the max unsigned value of bit width n.

- `(eo::zmod r1 r2)`
  - If `r1` and `r2` are numerals and `r2` is non-zero, then this returns the integer remainder of `r1` divided by `r2`.
  - If `r1` and `r2` are bit vector values of the same category and bit width, then this returns their (total, unsigned) remainder, where remainder by zero returns `r1`.

- `(eo::is_neg r1)`
  - If `r1` is an arithmetic value, this returns `true` if `r1` is strictly negative and `false` otherwise.

- `(eo::gt r1 r2)`

  is treated as `(eo::is_neg (eo::add (eo::neg r1) r2))`.

### String operators

- `(eo::len r1)`
  - Binary length (bit width) if `r1` is a binary value.
  - String length if `r1` is a string value.

- `(eo::concat r1 r2)`
  - The bit vector concatenation of `r1` and `r2` if they are both binary values.
  - The string concatenation of `r1` and `r2` if they are both are string values.

- `(eo::extract r1 r2 t3)`
  - If `r1` is a binary value and `r2` and `r3` are numerals, this returns the binary value corresponding to the bits in `r1` from position `r2` through `r3` if `r2` is non-negative, or the empty bit vector otherwise.<!--CT this may need revising -->
  - If `r1` is a string value and `r2` and `r3` are numerals, this returns the string value corresponding to the characters in `r1` from position `r2` through `r3` inclusive if `r2` is non-negative, or the empty string otherwise.

- `(eo::find r1 r2)`
  
  If `r1` and `r2` are string values, this returns the numeral corresponding to the first index (left to right) where `r2` occurs as a substring of `r1`, or the numeral value `-1` otherwise.

### Conversion operators

- `(eo::to_z r1)`
  - If `r1` is an numeral value $n$, this evaluates to $n$.
  - If `r1` is a rational value $r$, this evaluates to the numeral value corresponding to the floor of $r$ <!--CT this may need further clarification for the case when r is negative -->.
  - If `r1` is a binary value $b$, this evaluates to the numeral value corresponding to $b$ <!--CT signed or unsigned? -->.
  - If `r1` is a string value $s$ of length one, this evaluates the code point of $s$'s (only) character.

- `(eo::to_q r1)`
  - If `r1` is a rational value $r$, this evaluates to $r$.
  - If `r1` is a numeral value $n$, this evaluates the (integral) rational value corresponding to $n$.

- `(eo::to_bin r1 r2)`
  - If `r1` is a 32-bit numeral $w_1$ and `r2` is a binary value $b$ of bit width $w_2$, this evaluates to the binary value $b$ of bit width $w_1$.<!--CT This does not seem well-defined. What happens when w_1 < w_2 or w_1 > w_2?  Zero-extension? Truncation?-->
  - If `r1` is a 32-bit numeral $w$ and `r2` is a numeral $m$, this evaluates to the binary value of bit width $w$ corresponding to $(m \mod 2^w)$.

- `(eo::to_str r1)`
  - If `r1` is a string value $s$, this evaluates to $s$.
  - If `r1` is a numeral value $n$ specifying a code point from Unicode planes `0-2` (i.e., a numeral between `0` and `196607`), this evaluates to the string of length one whose character has code point $n$.
  - If `r1` is a rational or bit vector value $v$, this evaluates to the string value `"`$v$`"`. Note that if $v$ is a hexadecimal, it will contain lowercase letters for digits greater than `9`.
  - If `r1` is a decimal value $d$, this evaluates to [`(eo::to_str r)`] where `r` is the (normalized) rational corresponding to $d$.

The Ethos eagerly evaluates ground applications of computational operators.
In other words, the term `(eo::mul (eo::add 1 1) 3)` is syntactically equivalent in all contexts to `6`.
<!--CT Added -->
 In contrast, expressions like `(eo::add (+ 1 1) 3)` and `(eo::mul (eo::add 1 1) a)`, where `a` and `+` are user-declared symbols, evaluate to themselves since neither `(+ 1 1)` nor `a` are values.

The Ethos supports extensions of `eo::and, eo::or, eo::xor, eo::add, eo::mul, eo::concat` to an arbitrary number of arguments $ \geq 2$, with the expected semantics.

### Computation Examples

Here are a few examples of evaluations, where the syntax `t --> r` means that [`t`] is `r`.

```smt
(eo::and true false)         -->  false
(eo::and #b1110 #b0110)      -->  #b0110
(eo::or true false)          -->  true
(eo::xor true true)          -->  false
(eo::xor #b111 #b011)        -->  #b100
(eo::not true)               -->  false
(eo::not #b1010)             -->  #b0101
(eo::add 1 1)                -->  2
(eo::add 1 1 1 0)            -->  3
(eo::add 1/2 1/3)            -->  5/6
(eo::add 2 1/3)              -->  (eo::add 2 1/3)  ; no mixed arithmetic
(eo::add 2/1 1/3)            -->  7/3
(eo::add 2.0 1/3)            -->  (eo::add 2.0 1/3)  ; since no mixed arithmetic
(eo::add 2.0 2.5)            -->  4.5
(eo::add #b01 #b01)          -->  #b10
(eo::add #x1 #b0001)         -->  (eo::add #x1 #b0001)  ; since no mixed arithmetic
(eo::mul 2 7)                -->  14
(eo::mul 2 2 7)              -->  28
(eo::mul 1/2 1/4)            -->  1/8
(eo::neg -15)                -->  15
(eo::qdiv 12 6)              -->  3/1
(eo::qdiv 7 2)               -->  7/2
(eo::qdiv 7/1 2/1)           -->  7/2
(eo::qdiv 7.0 2.0)           -->  7/2
(eo::qdiv 7 0)               -->  (eo::qdiv 7 0)  ; no division by zero
(eo::zdiv 12 3)              -->  4
(eo::zdiv 7 2)               -->  3
(eo::is_neg 0)               -->  false
(eo::is_neg -7/2)            -->  true
(eo::len "abc")              -->  3
(eo::len """hi""")           -->  4
(eo::len "\u{AB0E}")         -->  1
(eo::len "\uA")              -->  3
(eo::len #b11100)            -->  5
(eo::concat "abc" "def")     -->  "abcdef"
(eo::concat #b000 #b11)      -->  #b00011
(eo::extract "abcdef" 0 1)   -->  "ab"
(eo::extract "abcdef" -1 3)  -->  ""
(eo::extract "abcdef" 1 10)  -->  "bcdef"
(eo::extract #b11100 2 4)    -->  #b111
(eo::extract #b11100 2 1)    -->  #b
(eo::extract #b111000 1 10)  -->  #b11100
(eo::extract #b10 -1 2)      -->  #b
(eo::find "abc" "bc")        -->  1
(eo::find "abc" "")          -->  0
(eo::find "abcdef" "g")      -->  -1
(eo::to_z 3/2)               -->  1
(eo::to_z 45)                -->  45
(eo::to_z "A")               -->  65
(eo::to_z "1")               -->  49
(eo::to_z "451")             -->  (eo::to_z "451")  ; string is not length one
(eo::to_z "")                -->  (eo::to_z "")  ; string is not length one
(eo::to_z "\u{9876}")        -->  9876
(eo::to_q 6)                 -->  6/1
(eo::to_bin 4 3)             -->  #b0011
(eo::to_bin 4 #b1)           -->  #b0001
(eo::to_bin 2 #b10101010)    -->  #b10
(eo::to_str 65)              -->  "A"
(eo::to_str 123)             -->  "{"
(eo::to_str -1)              -->  (eo::to_str -1) ; since not a valid code point
(eo::to_str 200000)          -->  (eo::to_str 200000) ; since not a valid code point
(eo::to_str 1/2)             -->  "1/2"
(eo::to_str #b101)           -->  "#b101"
```

### Core Computation Examples

```smt
(declare-type Int ())
(declare-const x Int)
(declare-const y Int)
(declare-const a Bool)
```

Note the following examples of core operators for the signature above:

```smt
(eo::is_eq 0 1)                     -->  false
(eo::is_eq x y)                     -->  false
(eo::is_eq x x)                     -->  true
(eo::requires x 0 true)             -->  (eo::requires x 0 true)  ; x and 0 are not syntactically equal
(eo::requires x x y)                -->  y
(eo::requires x x Int)              -->  Int
(eo::ite false x y)                 -->  y
(eo::ite true Bool Int)             -->  Bool
(eo::ite a x x)                     -->  (eo::ite a x x)  ; a is not a value

(eo::is_eq 2 (eo::add 1 1))         -->  true
(eo::is_eq x (eo::requires x 0 x))  -->  false
(eo::ite (eo::is_eq x 1) x y)       -->  y
```

In the above, it is important to note that `eo::is_eq` is a check for syntactic equality after evaluation.
It does not require that its arguments denote values, so for example `(eo::is_eq x y)` returns `false`.

<a name="list-computation"></a>

## List computations

Below, we assume that `f` is right associative operator with nil terminator `nil` and `t1, t2` are ground. Otherwise, the following operators do not evaluate.
We describe the evaluation for right associative operators; left associative evaluation is defined analogously.
We say that a term is an `f`-list with children `t1 ... tn` if it is of the form `(f t1 ... tn)` where `n>0` or `nil` if `n=0`.

### List operators

- `(eo::nil f)`
  - If `f` is a right associative operator, return its nil terminator.
- `(eo::cons f t1 t2)`
  - If `r2` is an `f`-list, then this returns the term `(f t1 t2)`.
- `(eo::list_len f t)`
  - If `t` is an `f`-list with children `t1 ... tn`, then this returns `n`.
- `(eo::list_concat f t1 t2)`
  - If `r1` is an `f`-list with children `t11 ... t1n` and `r2` is an `f`-list with children `t21 ... t2m`, this returns `(f t11 ... t1n t21 ... t2m)` if `n+m>0` and `nil` otherwise. Otherwise, this operator does not evaluate.
- `(eo::list_nth f t1 t2)`
  - If `f` is a right associative operator with nil terminator with nil terminator `nil`, `r1` is `(f s0 ... s{n-1})`, and `r2` is a numeral value such that `0<=t2<n`, then this returns `s_{t2}`. Otherwise, this operator does not evaluate.
- `(eo::list_find f t1 t2)`
  - If `f` is a right associative operator with nil terminator with nil terminator `nil` and `r1` is `(f s0 ... s{n-1})`, then this returns the smallest numeral value `i` such that `r2` is syntactically equal to `si`, or `-1` if no such `si` can be found. Otherwise, this operator does not evaluate.

### List Computation Examples

```smt
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
(declare-const a Bool)
(declare-const b Bool)
```

Given the signature above, the terms on both sides of the evaluation below are written in their form prior to desugaring, where recall that, e.g., `(or a)` after desugaring is `(or a false)` and `(or a b)` is `(or a (or b false))`.

```smt
(eo::nil or)  -->  false
(eo::nil a)   -->  (eo::nil a)                ; since a is not an associative operator

(eo::cons or a (or a b))         -->  (or a a b)
(eo::cons or false (or a b))     -->  (or false a b)
(eo::cons or (or a b) (or b))    -->  (or (or a b) b)
(eo::cons or false false)        -->  (or false)
(eo::cons or a b)                -->  (eo::cons or a b)                ; since b is not an or-list
(eo::cons or a (or b))           -->  (or a b)
(eo::cons and (or a b) (and b))  -->  (and (or a b) b)
(eo::cons and true (and a))      -->  (and a)
(eo::cons and (and a) true)      -->  (and (and a))

(eo::list_len or (or a b))         -->  2
(eo::list_len or (or (or a a) b))  -->  2
(eo::list_len or false)            -->  0
(eo::list_len or (and a b))        -->  (eo::list_len or (and a b))  ; since (and a b) is not an or-list

(eo::list_concat or false false)           -->  false
(eo::list_concat or (or a b) (or b))       -->  (or a b b)
(eo::list_concat or (or (or a a)) (or b))  -->  (or (or a a) b)
(eo::list_concat or false (or b))          -->  (or b)
(eo::list_concat or (or a b b) false)      -->  (or a b b)
(eo::list_concat or a (or b))              -->  (eo::list_concat or a (or b))         ; since a is not an or-list
(eo::list_concat or (or a) b)              -->  (eo::list_concat or (or a) b)         ; since b is not an or-list
(eo::list_concat or (or a) (or b))         -->  (or a b)
(eo::list_concat or (and a b) false)       -->  (eo::list_concat or (and a b) false)  ; since (and a b) is not an or-list

(eo::list_nth or (or a b a) 1)   -->  b
(eo::list_nth or (or a) 0)       -->  a
(eo::list_nth or false 0)        -->  (eo::list_nth or false 0)         ; since false has <=0 children
(eo::list_nth or (or a b a) 3)   -->  (eo::list_nth or (or a b a) 3)    ; since (or a b a) has <=3 children
(eo::list_nth or (and a b b) 0)  -->  (eo::list_nth or (and a b b) 0)   ; since (and a b b) is not an or-list

(eo::list_find or (or a b a) b)     -->  1
(eo::list_find or (or a b a) true)  -->  -1
(eo::list_find or (and a b b) a)    -->  (eo::find or (and a b b) a)      ; since (and a b b) is not an or-list
```

### Nil terminator with additional arguments

As we will introduce in [param-constants](#param-constants),
`eo::nil` is overloaded to accept addition arguments beyond the operator.
In particular, `(eo::nil or a b)` intuitively denotes the nil terminator
for the term `or` applied to arguments `a` and `b`.

### Example: Type rule for BitVector concatenation

```smt
(declare-type Int ())
(declare-consts <numeral> Int)
(declare-type BitVec (Int))

(declare-const concat (->
  (! Int :var n :implicit)
  (! Int :var m :implicit)
  (BitVec n)
  (BitVec m)
  (BitVec (eo::add n m))))

(declare-const x (BitVec 2))
(declare-const y (BitVec 3))
(define z () (concat x y) :type (BitVec 5))
```

Above, we define a type declaration for `BitVec` that expects an integer (i.e. denoting the bit width) as an argument.
Then, a type rule is given for bitvector concatenation `concat`, involves the result of invoking `eo::add` on the bit width of its two arguments.

Since `eo::add` only evaluates on numeral values, this means that this type rule will only give the intended result when the bit width arguments to this function are concrete.
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
(declare-type Int ())
(declare-consts <numeral> Int)
(declare-type BitVec (Int))

(declare-consts <binary> (BitVec (eo::len eo::self)))

(define x () #b000 :type (BitVec 3))
```

To define the class of binary values, whose type depends on the number of bits they contain, the Ethos provides support for a distinguished parameter `eo::self`.
The type checker for values applies the substitution mapping `eo::self` to the term being type checked.
This means that when type checking the binary constant `#b0000`, its type prior to evaluation is `(BitVec (eo::len #b0000))`, which evaluates to `(BitVec 4)`.

<a name="param-constants"></a>

## Parameterized constants

Recall that in [assoc-nil](#assoc-nil), when using `declare-const` to define associative operators with nil terminators, it is not possible to have the nil terminator for that operator depend on its type parameters.
In this section, we introduce a new command `declare-parameterized-const` which overcomes this limitation.
Its syntax is:

```smt
(declare-parameterized-const <symbol> (<typed-param>*) <type> > <attr>*)
```

In the following example,
we declare bitvector-or (`bvor` in SMT-LIB) where its nil terminator is bitvector zero for the given bit width.

```smt
(declare-type Int ())
(declare-consts <numeral>Int)                ; numeral literals denote Int constants
(declare-type BitVec (Int))
(declare-consts <binary>
    (BitVec (eo::len eo::self)))              ; binary literals denote BitVec constants of their length
(define bvzero ((m Int)) (eo::to_bin m 0))    ; returns the bitvector value zero for bit width m

(declare-parameterized-const bvor ((m Int))   ; bvor is parameterized by a bit width m
    (-> (BitVec m) (BitVec m) (BitVec m))
    :right-assoc-nil (bvzero m)               ; its nil terminator depends on m
)
```

In this example, we first declare the `Int` and `BitVec` sorts, and associate numeral and binary values with those sorts (see [declare-consts](#declare-consts)).
Then, we declare `bvor` using `declare-parameterized-const` where its parameter is an integer `m`.
The provided parameters are in scope for the remainder of the command, which means they can appear in the nil terminator of the operator.
Here, we specify `(bvzero m)` as the nil terminator for `bvor`.

The parameter list of a parameterized constant are treated as _implicit_ arguments.
In this example, the type of `bvor` is `(-> (! Int :var m :implicit) (BitVec m) (BitVec m) (BitVec m))`.

If a function `f` is given a nil terminator with free parameters, this impacts:

- how applications of `f` are desugared, and
- how list operations such as `eo::nil`, `eo::cons`, and `eo::list_concat` are computed for `f`.

For the former, say we apply `(f t1 ... tn)`, where `f` is right associative with nil terminator `nil`, where `nil` has free paramters `u1 ... um`.
Similar to the procedure described in [assoc-nil](#assoc-nil), if `tn` is not marked with `:list`, we insert the nil terminator of `f` to the end of the argument list.
To compute the parameters of the nil terminator, we first compute the type of `f` applied to arguments `t1 ... tn`.
If successful, this is the type `T [v1 ... vm / u1 ... um]` for some terms `v1 ... vm` and the given return type `T` of `f`.
If any of `v1 ... vm` is non-ground, or if the application fails to type check,
the nil terminator is `(eo::nil f t1 ... tn)`.
In other words, the computation of the nil terminator is deferred to this term (which itself may not evaluate).
Otherwise, the nil terminator is `nil[ v1 ... vm / u1 ... um]`.
Constructing `(f t1 ... tn)` then proceeds inductively via the same procedure described in [assoc-nil](#assoc-nil).
Examples of this are given in the following, assuming the declaration of `bvor` above.

```smt
(declare-const p (-> Bool Bool))
(define test ((x (BitVec 4)) (y (BitVec 4)) (n Int) (z (BitVec n)) (w (BitVec n)) (u (BitVec n) :list))
    ...
    (bvor x y)        ; (bvor x (bvor y #b0000))
    (bvor x)          ; (bvor x #b0000)
    (bvor z w)        ; (bvor z (bvor w (eo::nil bvor z w)))
    (bvor z u)        ; (bvor z u)
    (bvor u z)        ; (eo::list_concat bvor u (bvor z (eo::nil bvor u z)))
    ...
)
```

Above, notice that `x` and `y` have concrete bit widths and `z,w,u` have the free parameter `n` as their bit width.
In the first term, `(bvor x y)` is type checked to `(BitVec m)[4/m]`.
Since `4` is ground, we compute the nil terminator `(bvzero 4)`, which evaluates to `#b0000`.
This is then used as the nil terminator, since `y` is not marked with `:list`.
The second example is similar.

In the third, example, `(bvor z w)` is type checked to `(BitVec m)[n/m]`, where note that `n` is _not_ ground.
Thus, we do not compute its nil terminator and instead construct the placeholder `(eo::nil bvor z w)`.
This is then used as the nil terminator since `w` is not marked as `:list`.
In the fourth example, `(bvor z u)` is also type checked to `(BitVec m)[n/m]`, but in this case the nil terminator is not used since `u` is marked as `:list`.
In the fifth example, we use `eo::list_concat` as before since the list term `u` appears as the first argument.
Similar to the third example, a placeholder for the nil terminator is generated.

Any list operation involving `f` first requires computing the nil terminator in question.
This is done using the same procedure as described above.
If we do not infer a ground nil terminator, then the term does not evaluate.
Examples can be found at the end of this section.

Consider again the term `(bvor z w)` from the previous example:

```smt
(define test ((n Int) (z (BitVec n)) (w (BitVec n)))
    (bvor z w)        ; (bvor z (bvor w (eo::nil bvor z w)))
)
(declare-const a (BitVec 4))
(declare-const b (BitVec 4))
(define test4 () (test 4 a b))
```

The term in the body of `test` desugars to `(bvor z (bvor w (eo::nil bvor z w)))`, where
`(eo::nil bvor z w)` does not evaluate since the nil terminator of `(bvor z w)` involves a non-ground parameter `n`.
In this example, we instantiate this definition in the body of `test4`, where `n=4`, `z=a` and `w=b`.
The term `(bvor a (bvor b (eo::nil bvor a b)))` then evaluates to `(bvor a (bvor b #b0000)`, since the nil terminator of `(bvor a b)` has ground parameter `n=4` and evaluates to `#b0000`.

> __Note:__ Alternatively, the parameters of a function `f` may be provided explicitly using the syntax `(eo::_ f p1 ... pn)`.
When parameters are provided, these are used instead of the type inference method above.
Furthermore, these parameters are dropped when applying the operator to arguments.
For example `(_ (eo::_ bvor 4) a b)` is equivalent to `(bvor a (bvor b #b0000))` after desugaring.
An example use case for this feature is directly refer to the nil terminator of a concrete instance of `bvor`, e.g. `(eo::nil (eo::_ bvor 4))` evaluates to `#b0000`.

The following are examples of list operations when using parameterized constant `bvor`:

```smt
(declare-const a (BitVec 4))
(declare-const b (BitVec 4))
(declare-const c (BitVec 5))

(eo::nil bvor)                 -->  (eo::nil bvor)     ; since we cannot infer the type of bvor
(eo::nil bvor a)               -->  #b0000             ; since #b0000 is the nil terminator of (bvor a)
(eo::nil bvor a c)             -->  (eo::nil bvor a c) ; since (bvor a c) is ill-typed
(eo::nil (eo::_ bvor 4))       -->  #b0000

(eo::cons bvor a #b0000)             -->  (bvor a)
(eo::cons bvor c #b0000)            --> (eo::cons bvor c #b0000) ; since (bvor c #b0000) is ill-typed
(eo::cons bvor a (bvor a b))        --> (bvor a a b)

(eo::list_concat bvor #b0000 #b0000)       --> #b0000
(eo::list_concat bvor (bvor a b) (bvor b)) --> (bvor a b b)
```

> __Note:__ If no free parameters are used in the nil terminator of a parameterized constant, then it is treated equivalent to if it were declared via an ordinary declare-const command, and a warning is issued.

<a name="overloading"></a>

## Overloading

The Ethos supports symbol overloading.
For example, the following is accepted:

```smt
(declare-const - (-> Int Int))
(declare-const - (-> Int Int Int))
(declare-const - (-> Real Real Real))
```

When parsing a term whose head is `-`, the Ethos will automatically choose which symbol to use based on the arguments passed to it.
In particular, if a symbol is overloaded, the Ethos will use the first symbol that results in a well-typed term if applied.
For example, assuming standard definitions of SMT-LIB literal values,
`(- 1)` uses the first, `(- 0 1)` uses the second, and `(- 0.0 1.0)` uses the third.
If a symbol is unapplied, then the Ethos will interpret it as the first declared term for that symbol.

> __Note:__ When multiple variants are possible, the Ethos will use the first one and will _not_ throw a warning. This behavior permits the user to order the declarations in the order of their precedence. For example, the SMT-LIB operator for unary negation should be declared _before_ the declaration for subtraction. If this were done in the opposite order, then (- t) would be interpreted as the partial application of subtraction to the term t.

Furthermore, the Ethos supports an operator `eo::as` for disambiguation whose syntax is `(eo::as <term><type>)`.
A term of the form `(eo::as t (-> T1 ... Tn T))` evaluates to term `s` only if `(s k1 ... kn)` has type `T` where `k1 ... kn` are variables of type `T1 ... Tn`, and `t` and `s` are atomic terms with the same name.
If multiple such terms `s` exist, then the most recent one is returned.
Otherwise, the term `(eo::as t (-> T1 ... Tn T))` is unevaluated.
For example, `(eo::as - (-> Int Int Int))` evaluates to the second declared symbol in the example above.

## Declaring Proof Rules

The generic syntax for a `declare-rule` command accepted by `ethos` is:

```smt
(declare-rule <symbol> <keyword>? <sexpr>*)
```

When parsing this command, `ethos` will determine the format of the expected arguments based on the given keyword.
If the `<keyword>` is not provided, the we assume it has been marked `:ethos`.
All rules not marked with `:ethos` are not supported by the checker are unsupported and will cause the checker to terminate.

If the keyword is `:ethos`, then the expected syntax that follows is given below:

```smt
(declare-rule <symbol> :ethos (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? :conclusion <term> <attr>*)
where
<assumption>   ::= :assumption <term>
<premises>     ::= :premises (<term>*) | :premise-list <term> <term>
<arguments>    ::= :args (<term>*)
<reqs>         ::= :requires ((<term> <term>)*)
```

A proof rule begins by defining a list of free parameters, followed by 4 optional fields and a conclusion term.
These fields include:

- `<premises>`, denoting the premise patterns of the proof rule. This is either a list of formulas (via `:premises`) or the specification of list of premises via (via `:premise-list`), which will be described in detail later.
- `<arguments>`, denoting argument patterns of provide to a proof rule.
- `<reqs>`, denoting a list of pairs of terms.

Proof rules with assumptions `<assumption>` are used in proof with local scopes and will be discussed in detail later.

Proof rules may be marked with attributes at the end of their definition. 
The only attribute of this form that is currently supported is `:sorry`, which indicates that the proof rule does not have a formal justification.
This in turn impacts the response of the Ethos, as described in [responses](#responses).

At a high level, an application of a proof rule is given a concrete list of (premise) proofs, and a concrete list of (argument) terms.
A proof rule checks if a substitution `S` can be found such that:

- The formulas proven by the premise proofs match provided premise patterns under substitution `S`,
- The argument terms match the provided argument patterns under substitution `S`,
- The requirements are _satisfied_ under substitution `S`, namely, each pair of terms in the requirements list evaluates pairwise to the same term.
If these criteria are met, then the proof rule proves the result of applying `S` to the conclusion term.

A proof rule is only well defined if the free parameters of the requirements and conclusion term are also contained in the arguments and premises.

> __Note:__ Internally, proofs can be seen as terms whose type is given by a distinguished `Proof` type. In particular, `Proof` is a type whose kind is `(-> Bool Type)`, where the argument of this type is the formula that is proven. For example, `(Proof (> x 0))` is the proof that `x` is greater than zero. By design, the user cannot declare terms involving type `Proof`. Instead, proofs can only be constructed via the commands `assume` and `step` as we describe in [proofs](#proofs).

### Example rule: Reflexivity of equality

```smt
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

```smt
(declare-const = (-> (! Type :var T :implicit) T T Bool))
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
(declare-type Int ())
(declare-consts <numeral> Int)
(declare-const >= (-> Int Int Bool))
(declare-rule leq-contra ((x Int))
    :premise ((>= x 0))
    :requires (((eo::is_neg x) true))
    :conclusion false)
```

This rule expects an arithmetic inequality.
It requires that the left hand side of this inequality `x` is a negative numeral, which is checked via the requirement `:requires (((eo::is_neg x) true))`.

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
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-rule symm ((T Type) (t T) (s T))
    :premises ((= t s))
    :conclusion (= s t)
)
(declare-type Int ())
(declare-const a Int)
(declare-const b Int)
(assume @p0 (= a b))
(step @p1 (= b a) :rule symm :premises (@p0))
```

## Proofs with local assumptions

The Eunoia language includes commands `assume-push` and `step-pop` with the same syntax as `assume` and `step` respectively.
However, the former can be seen as introducing a local assumption that is consumed by the latter.
We give an example of this in following.

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

## Side Conditions

Similar to `declare-rule`, the Ethos supports an extensible syntax for programs whose generic syntax is given by:

```smt
(program <symbol> <keyword>? <sexpr>*)
```

When parsing this command, `ethos` will determine the format of the expected arguments based on the given keyword.
If the `<keyword>` is not provided, the we assume it has been marked `:ethos`.
All programs not marked with `:ethos` are not supported by the checker are unsupported and will cause the checker to terminate.

If the keyword is `:ethos`, then the expected syntax that follows is given below, and is used for defining recursive programs.
In particular, in the Ethos, a program is an ordered lists of rewrite rules.
The syntax for this command is as follows.

```smt
(program <symbol> :ethos (<typed-param>*) (<type>*) <type> ((<term> <term>)+))
```

This command declares a program named `<symbol>`.
The provided type parameters are implicit and are used to define its type signature and body.

The type of the program is given immediately after the parameter list, provided as a list of argument types and a return type.
The semantics of the program is given by a non-empty list of pairs of terms, which we call its _body_.
For program `f`, This list is expected to be a list of terms of the form `(((f t11 ... t1n) r1) ... ((f tm1 ... tmn) rm))`
where `t11...t1n, ..., tm1...tmn` do not contain computational operators.
A (ground) term `(f s1 ... sn)` evaluates by finding the first term in the first position of a pair of this list that matches it for substitution `S`, and returns the result of applying `S` to the right hand side of that pair.
If no such term can be found, then the application does not evaluate.

> __Note:__ Terms in program bodies are not statically type checked. Evaluating a program may introduce non-well-typed terms if the program body is malformed.

> __Note:__ For each case `((f ti1 ... tin) ri)` in the program body, the free parameters in `ri` are required to be a subset of the free parameters in `(f ti1 ... tin)`. Otherwise, an error is thrown.

> __Note:__ If a case is provided `(si ri)` in the definition of program `f` where `si` is not an application of `f`, an error is thrown.
Furthermore, if `si` contains any computational operators (i.e. those with `eo::` prefix), then an error is thrown.

### Example: Finding a child in an `or` term

The following program (recursively) computes whether a formula `l` is contained as the direct child of an application of `or`:

```smt
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
These parameters are used for defining the body of the program, but do _not_ necessarily coincide with the expected arguments to the program.
We then declare the type of the program `(Bool Bool) Bool`, i.e. the type of `contains` is a function expecting two Booleans and returning a Boolean.
The body of the program is then given in three cases.
First, terms of the form `(contains false l)` evaluate to `false`, that is, we failed to find `l` in the second argument.
Second, terms of the form `(contains (or l xs) l)` evaluate to `true`, that is we found `l` in the first position of the second argument.
Otherwise, terms of the form `(contains (or x xs) l)` evaluate in one step to `(contains xs l)`, in other words, we make a recursive call to find `l` in the tail of the list `xs`.

In this example, since `xs` was marked with `:list`, the terms `(or l xs)` and `(or x xs)` are desugared to terms where `xs` is matched with the tail of the input.
The next two examples show variants where an incorrect definition of this program is defined.

> __Note:__ As mentioned in [list-computation](#list-computation), Eunoia has dedicated support for operators over lists.
For the definition of `contains` in the above example, the term `(contains l c)` is equivalent to `(eo::not (eo::is_neg (eo::find or c l)))`.
Computing the latter is significantly faster in practice in the Ethos.

### Example: Finding a child in an `or` term (incorrect version)

```smt
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
In other words, these terms will match `or` terms with _exactly_ two children, for example `(contains (or a b) a)` will still evaluate to `true`.
However, `(contains (or a b c) a)` does not evaluate in this example.

### Example: Finding a child in an `or` term (incorrect version 2)

```smt
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
The Ethos will reject this definition since it implies that a computational operator appears in a pattern for matching.
In particular, the term `(or x xs)` is equivalent to `(eo::list_concat or x xs)` after desugaring.
Thus, the third case of the program, `(contains (eo::list_concat or x xs) l)`, is not a legal pattern.

### Example: Substitution

```smt
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
In detail, recall that the Ethos treats all function applications as curried (unary) applications.
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
  (S S U) U
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
(declare-type Int ())
(declare-consts <numeral> Int)
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const + (-> Int Int Int))
(declare-const - (-> Int Int Int))
(declare-const < (-> Int Int Bool))
(declare-const <= (-> Int Int Bool))

(program run_evaluate ((T Type) (U Type) (S Type) (a T) (b U) (z S))
    (S) S
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
(declare-type Int ())
(declare-type Real ())
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

```smt
(declare-type String ())
(declare-consts <string> String)
(declare-const not (-> Bool Bool))
(declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)

(program to_drat_lit ((l Bool))
  (Bool) Int
  (
    ((to_drat_lit (not l))  (eo::neg (eo::hash l)))
    ((to_drat_lit l)        (eo::hash l))
  )
)
(program to_drat_clause ((l Bool) (C Bool :list))
  (Bool) String
  (
    ((to_drat_clause false)    "0")
    ((to_drat_clause (or l C)) (eo::concat (eo::to_str (to_drat_lit l)) " " (to_drat_clause C)))
    ((to_drat_clause l)        (eo::concat (eo::to_str (to_drat_lit l)) " 0"))
  )
)
(program to_dimacs ((C Bool) (F Bool :list))
  (Bool) String
  (
    ((to_dimacs true)       "")
    ((to_dimacs (and C F))  (eo::concat (to_drat_clause C) " " (to_dimacs F)))
  )
)
```

The above program `to_dimacs` converts an SMT formula into DIMACS form, where `eo::hash` is used to assign atoms to integer identifiers.

### Match statements

The Ethos supports an operator `eo::match` for performing pattern matching on a target term. The syntax of this term is:

```smt
(eo::match (<typed-param>*) <term> ((<term> <term>)*))
```

The term `(eo::match (...) t ((s1 r1) ... (sn rn)))` finds the first term `si` in the list `s1 ... sn` that `t` can be matched with under some substitution and returns the result of applying that substitution to `ri`.

> __Note:__  Match terms require the free parameters of `ri` are a subset of the provided parameter list.
In other words, all patterns must only involve parameters that are locally bound as the first argument of the match term.
Also, similar to programs, the free parameters of `ri` that occur in the parameter list must be a subset of `si`, or else an error is thrown.

> __Note:__ Like programs, match terms are not statically type checked.

### Examples of legal and illegal match terms

```smt
(declare-type Int ())
(declare-const F Bool)
(declare-const a Int)
(declare-const P (-> Int Bool))
(declare-const f (-> Int Int))
; Legal match terms:
(define test1 ((x Int))
    (f (eo::match ((y Int)) x 
            (
                (a a) 
                (b b) 
                ((f (f a)) a)   ; can use arbitrary nesting in pattern terms
                ((f (f y)) b)
                (y a)           ; note that using a parameter as a pattern acts as a default case
            )
        )))
(define test2 ((F Bool) (y Int)) 
    (eo::match ((x Int)) F 
        (
            ((P x) y)           ; ok since y is bound at a higher scope and x is bound locally
        )
    ))

; Illegal match terms:
(define test3 ((F Bool) (y Int)) 
    (eo::match ((x Int)) F 
        (
            ((P y) a)       ; since y is not locally bound
        )
    ))
(define test4 ((F Bool) (y Int)) 
    (eo::match ((x Int)) F 
        (
            ((P a) x)       ; since x does not occur in (P a)
        )))  
```

### Example: Proof rule for symmetry of (dis)equality

```smt
(declare-type Int ())
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const not (-> Bool Bool))
(declare-rule symm ((F Bool))
    :premises (F)
    :conclusion
        (eo::match ((t1 Int) (t2 Int)) F
            (
                ((= t1 t2)       (= t2 t1))
                ((not (= t1 t2)) (not (= t2 t1)))
            )
        )
)
```

The above rule performs symmetry on equality or disequality.
It matches the given premise `F` with either `(= t1 t2)` or `(not (= t1 t2))` and flips the terms on the sides of the (dis)equality.

Internally, the semantics of `eo::match` can be seen as an (inlined) program applied to its head, such that the above example is equivalent to:

```smt
(declare-type Int ())
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

> __Note:__ The Ethos checker automatically performs the above transformation on match terms for consistency.
In more general cases, if the body of the match term contains free variables, these are added to the argument list of the internally generated program.

### Example: Proof rule for transitivity of equality with a premise list

```smt
(declare-type Int ())
(declare-const = (-> (! Type :var T :implicit) T T Bool))
(declare-const and (-> Bool Bool Bool) :left-assoc)

(program mk_trans ((t1 Int) (t2 Int) (t3 Int) (t4 Int) (tail Bool :list))
    (Int Int Bool) Bool
    (
        ((mk_trans t1 t2 (and (= t3 t4) tail)) (eo::requires t2 t3 (mk_trans t1 t4 tail)))
        ((mk_trans t1 t2 true)                 (= t1 t2))
    )
)

(declare-rule trans (E Bool))
    :premise-list E and
    :conclusion
        (eo::match ((t1 Int) (t2 Int) (tail Bool :list)) E
        (
            ((and (= t1 t2) tail) (mk_trans t1 t2 tail))
        ))
)
```

For simplicity, the rule is given only for equalities of the integer sort, although this rule can be generalized.
The proof rule `trans` first packages an arbitrary number of premises, constructs a conjunction of these premises, which to bound to `E` and passed to the match term in the conclusion.
The recursive calls in the side condition `mk_trans` accumulate the endpoints of an equality chain and ensure via `eo::requires` that further equalities extend the left hand side of this chain.

## Including and referencing files

The Ethos supports the following commands for file inclusion:

- `(include <string>)`, which includes the file indicated by the given string. The path to the file is taken relative to the directory of the file that includes it.
- `(reference <string> <symbol>?)`, which similar to `include` includes the file indicated by the given string, and furthermore marks that file as being the _reference input_ for the current run of the checker (see below). The optional symbol can refer to a normalization routine (see below).

### Validation Proofs via Reference Inputs

When the Ethos encounters a command of the form `(reference <string>)`, the checker enables a further set of checks that ensures that all assumptions in proofs correspond to assertions from the file referenced by the given string.

In particular, when the command `(reference "file.smt2")` is read, the Ethos will parse `file.smt2`.
The definitions and declaration commands in this file will be treated as normal, that is, they will populate the symbol table of the Ethos as they normally would if they were to appear in an `*.eo` input.
The commands of the form `(assert F)` will add `F` to a set of formulas we will refer to as the _reference assertions_.
Other commands in `file.smt2` (e.g. `set-logic`, `set-option`, and so on) will be ignored.

If ethos has read a reference file, then for each command of the form `(assume <symbol> G)`, ethos will check whether `G` occurs in the set of parsed reference assertions.
If it does not, then an error is thrown indicating that the proof is assuming a formula that is not a part of the original input.

> __Note:__ Only one reference command can be executed for each run of ethos.

> __Note:__ Incremental `*.smt2` inputs are not supported as reference files in the current version of ethos.

### Validation up to Normalization

Since the validation is relying on the fact that ethos can faithfully parse the original *.smt2 file, validation will only succeed if the signatures used by the Ethos exactly match the syntax for terms in the *.smt2 file.
Minor changes in how terms are represented will lead to mismatches.
For this reason, ethos additionally supports providing an optional normalization routine via `(reference <string> <term>)`, which includes the file indicated by the given string and specifies all assumptions must match an assertion after running the provided normalization function.

For example:

```smt
(declare-type Int ())
(declare-type Real ())
(declare-const / (-> Int Int Real))
(program normalize ((T Type) (S Type) (f (-> S T)) (x S) (a Int) (b Int))
   (T) T
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
The above program will be invoked on all formulas occurring in `assert` commands in `"file.smt2"` and subsequently formulas in `assume` commands.

## Oracles

The Ethos supports a command, `declare-oracle-fun`, which associates the semantics of a function with an external binary.
We reference to such functions as _oracle functions_.
The syntax and semantics of such functions are described in this [paper](https://homepage.divms.uiowa.edu/~ajreynol/vmcai22a.pdf).

In particular, the Ethos supports the command:

```smt
(declare-oracle-fun <symbol> (<type>*) <type> <symbol>)
```

Like the `declare-fun` command from SMT-LIB, this command declares a constant named `<symbol>` whose type is given by the argument types and return type.
In addition, a symbol is provided at the end of the command which specifies the name of executable command to run.
Ground applications of oracle functions are eagerly evaluated by invoking the binary and parsing its result, which we describe in more detail in the following.

### Example: Oracle isPrime

```smt
(declare-type Int ())
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
Otherwise, `(runIsPrime z)` evaluates to the result of parsing its output using the current parser state.
In this example, an output of response of `true` (resp. `false`) from the executable will be parsed back at the Boolean value `true` (resp. `false`).
More generally, input and output of oracles may contain symbols that are defined in the current parser state.
The user is responsible that the input can be properly parsed by the oracle, and the outputs of oracles can be properly parsed by the Ethos.

In the above example, a proof rule is then defined that says that if `z` is an integer greater than or equal to `2`, is the product of two integers `x` and `y`, and is prime based on invoking `runIsPrime` in the given requirement, then we can conclude `false`.

<a name="responses"></a>

## Checker Response

After successfully parsing an input file with no errors, the Ethos will respond with one of two possibilities:

- `incomplete` if it parsed any `step` or `step-pop` application that referenced a proof rule that was marked with the attribute `:sorry`, or
- `correct` otherwise.

Note however that Ethos does not impose any requirements on _what_ was proven in the proof.
The user is responsible for ensure that e.g. the proof contains a step with a desired conclusion (e.g. `false`).

## Appendix

### Command line options of ethos

The Ethos command line interface can be invoked by `ethos <option>* <file>` where `<option>` is one of the following:

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

The following options impact how proof files and reference files are parsed only (for details on classifications of files, see [full-syntax](#full-syntax)).
They do not impact how signature files (*.eo) are parsed:

- `--binder-fresh`: binders generate fresh variables.
- `--normalize-num`: treat numeral literals as syntax sugar for (integral) rational literals.
- `--no-normalize-dec`: do not treat decimal literals as syntax sugar for rational literals.
- `--no-normalize-hex`: do not treat hexadecimal literals as syntax sugar for binary literals.
- `--no-parse-let`: do not treat `let` as a builtin symbol for specifying a macro.

<a name="full-syntax"></a>

## Full syntax for Eunoia commands

Below defines the syntax accepted by the Ethos parser.

We distinguish three kinds of file inputs:

- _Proof files_ are files that are given via command line option that do _not_ have extension `*.eo`.
Their expected syntax is `<eo-command>*`.
- _Reference files_ are files included via the `reference` command.
Their expected syntax is `<smtlib2-command>*`.
- _Signature files_ are files that given via command line option that have extension `*.eo`, or those that are included via the command `include`.

As mentioned, the first two kinds of file inputs take into account options concerning the normalization of terms (e.g. `--normalize-num`), while signature files do not.
When streaming input to Ethos, we assume the input is being given for a proof file.

```bnf
;;;
<eo-command> ::=
    (assume <symbol> <term>) |
    (assume-push <symbol> <term>) |
    (declare-consts <lit-category> <type>) |
    (declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*) |
    (declare-oracle-fun <symbol> (<type>*) <type> <symbol>) |
    (declare-rule <symbol> <keyword> <sexpr>*) |
    (declare-rule <symbol> (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? :conclusion <term> <attr>*) |
    (declare-type <symbol> (<type>*)) |
    (define <symbol> (<typed-param>*) <term>) |
    (define-type <symbol> (<type>*) <type>) |
    (include <string>) |
    (program <symbol> <keyword> <sexpr>*) |
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
    (echo <string>?) |
    (exit) |
    (reset)

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
    (set-option <attr>) |
    <common-command>

;;;
<keyword>       ::= :<symbol>
<attr>          ::= <keyword> <term>?
<term>          ::= <symbol> | (<symbol> <term>+) | (! <term> <attr>+) | (eo::match (<typed-param>*) <term> ((<term> <term>)*))
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

 <a name="non-core-eval"></a>

### Definitions of Non-Core Evaluation Operators

The following signature can be used to define operators that are not required to be supported as core evaluation operators.

```smt
; Returns true if x is a numeral literal.
(define eo::is_z ((T Type :implicit) (x T))
  (eo::is_eq (eo::to_z x) x))

; Returns true if x is a rational literal.
(define eo::is_q ((T Type :implicit) (x T))
  (eo::is_eq (eo::to_q x) x))

; Returns true if x is a binary literal.
(define eo::is_bin ((T Type :implicit) (x T))
  (eo::is_eq (eo::to_bin (eo::len x) x) x))

; Returns true if x is a string literal.
(define eo::is_str ((T Type :implicit) (x T))
  (eo::is_eq (eo::to_str x) x))

; Returns true if x is a Boolean literal.
(define eo::is_bool ((T Type :implicit) (x T))
  (eo::ite (eo::is_eq x true) true (eo::is_eq x false)))

; Returns true if x is a variable.
(define eo::is_var ((T Type :implicit) (x T))
  (eo::is_eq (eo::var (eo::nameof x) (eo::typeof x)) x))

; Compare arithmetic greater than. Assumes x and y are values.
; Returns true if x > y.
(define eo::gt ((T Type :implicit) (x T) (y T))
  (eo::is_neg (eo::add (eo::neg x) y)))

; An arbitrary deterministic comparison of terms. Returns true if a > b based
; on this ordering.
(define eo::cmp ((T Type :implicit) (U Type :implicit) (a T) (b U))
  (eo::is_neg (eo::add (eo::hash b) (eo::neg (eo::hash a)))))

```

### Proofs as terms

This section overviews the semantics of proofs in the Eunoia language.
Proof checking can be seen as a special instance of type checking terms involving the `Proof` and `Quote` types.
The type system of the Ethos can be summarized as follows, where `t : S` are assumed axioms for all atomic terms `t` of type `S`:

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
(declare-const s
    (-> (! T1 :var v1 :implicit) ... (! Ti :var vi :implicit)
        (Proof p1) ... (Proof pn)
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
