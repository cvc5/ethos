//! The kinds of literals and the builtin `eo::` operators.
//!
//! A subset of `crates/pathos-term/src/kind.rs` of pathos (as of its commit
//! acae6aa): the two enums the compiled checker uses, and the two
//! predicates on operators. The kinds of symbols and of compound terms, the
//! flat `Kind`, the tables of names and the snapshot codes are left out; a
//! later sync with pathos copies only what is here.

/// The kinds of literals.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum LitKind {
    Boolean,
    Numeral,
    Decimal,
    Rational,
    Hexadecimal,
    Binary,
    String,
}

/// The builtin `eo::` operators.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum EvalOp {
    // core
    IsOk,
    IsEq,
    IfThenElse,
    Requires,
    Hash,
    TypeOf,
    NameOf,
    Compare,
    Log,
    // testers
    IsZ,
    IsQ,
    IsBin,
    IsStr,
    IsBool,
    IsVar,
    // equality
    Eq,
    // lists
    Nil,
    Cons,
    ListLength,
    ListConcat,
    ListNth,
    ListFind,
    ListErase,
    ListEraseAll,
    ListRev,
    ListSetof,
    ListMinclude,
    ListMeq,
    ListDiff,
    ListInter,
    ListSingletonElim,
    ListSingletonIntro,
    ListRepeat,
    // boolean
    Not,
    And,
    Or,
    Xor,
    // arithmetic
    Add,
    Neg,
    Mul,
    Pow,
    IntDiv,
    IntMod,
    RatDiv,
    IsNeg,
    Gt,
    // strings
    Length,
    Concat,
    Extract,
    Find,
    // conversions
    ToInt,
    ToRat,
    ToBin,
    ToString,
    // datatypes
    DtConstructors,
    DtSelectors,
}

impl EvalOp {

    /// Whether the operator takes two or more arguments in the input
    /// language, e.g. `(eo::add 1 2 3)`.
    pub fn is_nary(self) -> bool {
        matches!(
            self,
            EvalOp::Add | EvalOp::Mul | EvalOp::And | EvalOp::Or | EvalOp::Xor | EvalOp::Concat
        )
    }

    /// Whether this is one of the list operators.
    pub fn is_list_op(self) -> bool {
        matches!(
            self,
            EvalOp::Nil
                | EvalOp::Cons
                | EvalOp::ListLength
                | EvalOp::ListConcat
                | EvalOp::ListNth
                | EvalOp::ListFind
                | EvalOp::ListErase
                | EvalOp::ListEraseAll
                | EvalOp::ListRev
                | EvalOp::ListSetof
                | EvalOp::ListMinclude
                | EvalOp::ListMeq
                | EvalOp::ListDiff
                | EvalOp::ListInter
                | EvalOp::ListSingletonElim
                | EvalOp::ListSingletonIntro
                | EvalOp::ListRepeat
        )
    }
}
