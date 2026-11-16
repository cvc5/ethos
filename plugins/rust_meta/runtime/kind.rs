//! The kinds of terms.
//!
//! Ethos has one flat `Kind` enum. Here the kinds are grouped by what a term
//! of that kind carries (see [`crate::TermData`]): symbols carry a name,
//! literals a value, nodes and `eo::` operators a list of children. [`Kind`]
//! puts the groups back together for code that treats all terms alike, such
//! as matching and printing.

use std::fmt;

/// The kinds of named symbols.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum SymbolKind {
    Param,
    Const,
    /// `_`, `->`, `eo::add`, `as`, ...: only seen while parsing.
    BuiltinConst,
    ProgramConst,
    ProofRule,
}

impl SymbolKind {
    pub const ALL: &'static [SymbolKind] = &[
        SymbolKind::Param,
        SymbolKind::Const,
        SymbolKind::BuiltinConst,
        SymbolKind::ProgramConst,
        SymbolKind::ProofRule,
    ];
}

/// The kinds of literals.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum LitKind {
    Boolean,
    Numeral,
    Decimal,
    Rational,
    Hexadecimal,
    Binary,
    String,
}

impl LitKind {
    pub const ALL: &'static [LitKind] = &[
        LitKind::Boolean,
        LitKind::Numeral,
        LitKind::Decimal,
        LitKind::Rational,
        LitKind::Hexadecimal,
        LitKind::Binary,
        LitKind::String,
    ];
}

/// The kinds of compound terms other than `eo::` operator applications.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum NodeKind {
    FunctionType,
    ProgramType,
    QuoteType,
    Apply,
    Lambda,
    Tuple,
    Program,
    /// `(eo::as t T)`, where `T` is the type of `t`.
    As,
    /// SMT-LIB `(as t T)`, where `T` is the return type of `t`.
    AsReturn,
    Parameterized,
    ApplyOpaque,
    /// `(eo::pf F)`.
    Proof,
    /// `(eo::var "name" T)`.
    Variable,
}

impl NodeKind {
    pub const ALL: &'static [NodeKind] = &[
        NodeKind::FunctionType,
        NodeKind::ProgramType,
        NodeKind::QuoteType,
        NodeKind::Apply,
        NodeKind::Lambda,
        NodeKind::Tuple,
        NodeKind::Program,
        NodeKind::As,
        NodeKind::AsReturn,
        NodeKind::Parameterized,
        NodeKind::ApplyOpaque,
        NodeKind::Proof,
        NodeKind::Variable,
    ];

    /// Whether a term of this kind can have `n` children. These are the
    /// numbers the checker builds terms with and relies on when it takes
    /// them apart: a lambda has its variables and its body, a parameterized
    /// term its parameters and its head, a proof its formula, a quoted type
    /// its term, and an application at least a head. The other kinds are
    /// built with any number.
    pub fn takes(self, n: usize) -> bool {
        match self {
            NodeKind::Lambda | NodeKind::Parameterized => n == 2,
            NodeKind::Proof | NodeKind::QuoteType => n == 1,
            NodeKind::Apply | NodeKind::ApplyOpaque => n >= 1,
            _ => true,
        }
    }
}

/// The builtin `eo::` operators.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
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
    /// All operators with the name they have after `eo::`.
    pub const ALL: &'static [(EvalOp, &'static str)] = &[
        (EvalOp::IsOk, "is_ok"),
        (EvalOp::IsEq, "is_eq"),
        (EvalOp::IfThenElse, "ite"),
        (EvalOp::Requires, "requires"),
        (EvalOp::Hash, "hash"),
        (EvalOp::TypeOf, "typeof"),
        (EvalOp::NameOf, "nameof"),
        (EvalOp::Compare, "cmp"),
        (EvalOp::Log, "log"),
        (EvalOp::IsZ, "is_z"),
        (EvalOp::IsQ, "is_q"),
        (EvalOp::IsBin, "is_bin"),
        (EvalOp::IsStr, "is_str"),
        (EvalOp::IsBool, "is_bool"),
        (EvalOp::IsVar, "is_var"),
        (EvalOp::Eq, "eq"),
        (EvalOp::Nil, "nil"),
        (EvalOp::Cons, "cons"),
        (EvalOp::ListLength, "list_len"),
        (EvalOp::ListConcat, "list_concat"),
        (EvalOp::ListNth, "list_nth"),
        (EvalOp::ListFind, "list_find"),
        (EvalOp::ListErase, "list_erase"),
        (EvalOp::ListEraseAll, "list_erase_all"),
        (EvalOp::ListRev, "list_rev"),
        (EvalOp::ListSetof, "list_setof"),
        (EvalOp::ListMinclude, "list_minclude"),
        (EvalOp::ListMeq, "list_meq"),
        (EvalOp::ListDiff, "list_diff"),
        (EvalOp::ListInter, "list_inter"),
        (EvalOp::ListSingletonElim, "list_singleton_elim"),
        (EvalOp::ListSingletonIntro, "list_singleton_intro"),
        (EvalOp::ListRepeat, "list_repeat"),
        (EvalOp::Not, "not"),
        (EvalOp::And, "and"),
        (EvalOp::Or, "or"),
        (EvalOp::Xor, "xor"),
        (EvalOp::Add, "add"),
        (EvalOp::Neg, "neg"),
        (EvalOp::Mul, "mul"),
        (EvalOp::Pow, "pow"),
        (EvalOp::IntDiv, "zdiv"),
        (EvalOp::IntMod, "zmod"),
        (EvalOp::RatDiv, "qdiv"),
        (EvalOp::IsNeg, "is_neg"),
        (EvalOp::Gt, "gt"),
        (EvalOp::Length, "len"),
        (EvalOp::Concat, "concat"),
        (EvalOp::Extract, "extract"),
        (EvalOp::Find, "find"),
        (EvalOp::ToInt, "to_z"),
        (EvalOp::ToRat, "to_q"),
        (EvalOp::ToBin, "to_bin"),
        (EvalOp::ToString, "to_str"),
        (EvalOp::DtConstructors, "dt_constructors"),
        (EvalOp::DtSelectors, "dt_selectors"),
    ];

    /// The name after `eo::`, e.g. `add`.
    pub fn name(self) -> &'static str {
        EvalOp::ALL[self as usize].1
    }

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

    /// The name of the Ethos kind, e.g. `EVAL_ADD`.
    fn kind_name(self) -> &'static str {
        match self {
            EvalOp::IsOk => "EVAL_IS_OK",
            EvalOp::IsEq => "EVAL_IS_EQ",
            EvalOp::IfThenElse => "EVAL_IF_THEN_ELSE",
            EvalOp::Requires => "EVAL_REQUIRES",
            EvalOp::Hash => "EVAL_HASH",
            EvalOp::TypeOf => "EVAL_TYPE_OF",
            EvalOp::NameOf => "EVAL_NAME_OF",
            EvalOp::Compare => "EVAL_COMPARE",
            EvalOp::Log => "EVAL_LOG",
            EvalOp::IsZ => "EVAL_IS_Z",
            EvalOp::IsQ => "EVAL_IS_Q",
            EvalOp::IsBin => "EVAL_IS_BIN",
            EvalOp::IsStr => "EVAL_IS_STR",
            EvalOp::IsBool => "EVAL_IS_BOOL",
            EvalOp::IsVar => "EVAL_IS_VAR",
            EvalOp::Eq => "EVAL_EQ",
            EvalOp::Nil => "EVAL_NIL",
            EvalOp::Cons => "EVAL_CONS",
            EvalOp::ListLength => "EVAL_LIST_LENGTH",
            EvalOp::ListConcat => "EVAL_LIST_CONCAT",
            EvalOp::ListNth => "EVAL_LIST_NTH",
            EvalOp::ListFind => "EVAL_LIST_FIND",
            EvalOp::ListErase => "EVAL_LIST_ERASE",
            EvalOp::ListEraseAll => "EVAL_LIST_ERASE_ALL",
            EvalOp::ListRev => "EVAL_LIST_REV",
            EvalOp::ListSetof => "EVAL_LIST_SETOF",
            EvalOp::ListMinclude => "EVAL_LIST_MINCLUDE",
            EvalOp::ListMeq => "EVAL_LIST_MEQ",
            EvalOp::ListDiff => "EVAL_LIST_DIFF",
            EvalOp::ListInter => "EVAL_LIST_INTER",
            EvalOp::ListSingletonElim => "EVAL_LIST_SINGLETON_ELIM",
            EvalOp::ListSingletonIntro => "EVAL_LIST_SINGLETON_INTRO",
            EvalOp::ListRepeat => "EVAL_LIST_REPEAT",
            EvalOp::Not => "EVAL_NOT",
            EvalOp::And => "EVAL_AND",
            EvalOp::Or => "EVAL_OR",
            EvalOp::Xor => "EVAL_XOR",
            EvalOp::Add => "EVAL_ADD",
            EvalOp::Neg => "EVAL_NEG",
            EvalOp::Mul => "EVAL_MUL",
            EvalOp::Pow => "EVAL_POW",
            EvalOp::IntDiv => "EVAL_INT_DIV",
            EvalOp::IntMod => "EVAL_INT_MOD",
            EvalOp::RatDiv => "EVAL_RAT_DIV",
            EvalOp::IsNeg => "EVAL_IS_NEG",
            EvalOp::Gt => "EVAL_GT",
            EvalOp::Length => "EVAL_LENGTH",
            EvalOp::Concat => "EVAL_CONCAT",
            EvalOp::Extract => "EVAL_EXTRACT",
            EvalOp::Find => "EVAL_FIND",
            EvalOp::ToInt => "EVAL_TO_INT",
            EvalOp::ToRat => "EVAL_TO_RAT",
            EvalOp::ToBin => "EVAL_TO_BIN",
            EvalOp::ToString => "EVAL_TO_STRING",
            EvalOp::DtConstructors => "EVAL_DT_CONSTRUCTORS",
            EvalOp::DtSelectors => "EVAL_DT_SELECTORS",
        }
    }
}

/// The kind of any term.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Kind {
    Type,
    BoolType,
    /// An unknown, standing for any term; non-ground and evaluatable.
    Any,
    /// Ethos's null expression, of kind `NONE`. Ethos puts it into a term
    /// where it failed to compute a part, such as the constructor term of a
    /// `:chainable` operator; such terms do not type check.
    Null,
    Symbol(SymbolKind),
    Lit(LitKind),
    Node(NodeKind),
    Eval(EvalOp),
}

impl Kind {
    pub const PARAM: Kind = Kind::Symbol(SymbolKind::Param);
    pub const CONST: Kind = Kind::Symbol(SymbolKind::Const);
    pub const BUILTIN_CONST: Kind = Kind::Symbol(SymbolKind::BuiltinConst);
    pub const PROGRAM_CONST: Kind = Kind::Symbol(SymbolKind::ProgramConst);
    pub const PROOF_RULE: Kind = Kind::Symbol(SymbolKind::ProofRule);

    pub const BOOLEAN: Kind = Kind::Lit(LitKind::Boolean);
    pub const NUMERAL: Kind = Kind::Lit(LitKind::Numeral);
    pub const DECIMAL: Kind = Kind::Lit(LitKind::Decimal);
    pub const RATIONAL: Kind = Kind::Lit(LitKind::Rational);
    pub const HEXADECIMAL: Kind = Kind::Lit(LitKind::Hexadecimal);
    pub const BINARY: Kind = Kind::Lit(LitKind::Binary);
    pub const STRING: Kind = Kind::Lit(LitKind::String);

    pub const FUNCTION_TYPE: Kind = Kind::Node(NodeKind::FunctionType);
    pub const PROGRAM_TYPE: Kind = Kind::Node(NodeKind::ProgramType);
    pub const QUOTE_TYPE: Kind = Kind::Node(NodeKind::QuoteType);
    pub const APPLY: Kind = Kind::Node(NodeKind::Apply);
    pub const LAMBDA: Kind = Kind::Node(NodeKind::Lambda);
    pub const TUPLE: Kind = Kind::Node(NodeKind::Tuple);
    pub const PROGRAM: Kind = Kind::Node(NodeKind::Program);
    pub const AS: Kind = Kind::Node(NodeKind::As);
    pub const AS_RETURN: Kind = Kind::Node(NodeKind::AsReturn);
    pub const PARAMETERIZED: Kind = Kind::Node(NodeKind::Parameterized);
    pub const APPLY_OPAQUE: Kind = Kind::Node(NodeKind::ApplyOpaque);
    pub const PROOF: Kind = Kind::Node(NodeKind::Proof);
    pub const VARIABLE: Kind = Kind::Node(NodeKind::Variable);

    /// Whether terms of this kind are user-visible named symbols. Builtin
    /// constants are not, as in Ethos's `isSymbol`.
    pub fn is_symbol(self) -> bool {
        matches!(self, Kind::Symbol(k) if k != SymbolKind::BuiltinConst)
    }

    pub fn is_literal(self) -> bool {
        matches!(self, Kind::Lit(_))
    }

    pub fn is_literal_op(self) -> bool {
        matches!(self, Kind::Eval(_))
    }

    /// How a term of this kind is written as the head of an s-expression in
    /// printed terms, e.g. `->` or `eo::add`.
    pub fn to_term_string(self) -> String {
        match self {
            Kind::Type => "Type".into(),
            Kind::BoolType => "Bool".into(),
            Kind::Any => "eo::?".into(),
            Kind::Null => "[NONE]".into(),
            Kind::Node(n) => match n {
                NodeKind::FunctionType => "->".into(),
                NodeKind::ProgramType => "eo::arrow".into(),
                NodeKind::QuoteType => "eo::quote".into(),
                NodeKind::Tuple => "eo::tuple".into(),
                NodeKind::Apply | NodeKind::ApplyOpaque => "_".into(),
                NodeKind::Lambda => "lambda".into(),
                NodeKind::Program => "program".into(),
                NodeKind::As => "eo::as".into(),
                NodeKind::AsReturn => "as".into(),
                NodeKind::Parameterized => "eo::_".into(),
                NodeKind::Proof => "eo::pf".into(),
                NodeKind::Variable => "eo::var".into(),
            },
            Kind::Eval(op) => format!("eo::{}", op.name()),
            Kind::Symbol(_) | Kind::Lit(_) => format!("[{self}]"),
        }
    }
}

impl fmt::Display for Kind {
    /// The name of the kind in Ethos, e.g. `APPLY`; used in error messages.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Kind::Type => "TYPE",
            Kind::BoolType => "BOOL_TYPE",
            Kind::Any => "ANY",
            Kind::Null => "NONE",
            Kind::Symbol(s) => match s {
                SymbolKind::Param => "PARAM",
                SymbolKind::Const => "CONST",
                SymbolKind::BuiltinConst => "BUILTIN_CONST",
                SymbolKind::ProgramConst => "PROGRAM_CONST",
                SymbolKind::ProofRule => "PROOF_RULE",
            },
            Kind::Lit(l) => match l {
                LitKind::Boolean => "BOOLEAN",
                LitKind::Numeral => "NUMERAL",
                LitKind::Decimal => "DECIMAL",
                LitKind::Rational => "RATIONAL",
                LitKind::Hexadecimal => "HEXADECIMAL",
                LitKind::Binary => "BINARY",
                LitKind::String => "STRING",
            },
            Kind::Node(n) => match n {
                NodeKind::FunctionType => "FUNCTION_TYPE",
                NodeKind::ProgramType => "PROGRAM_TYPE",
                NodeKind::QuoteType => "QUOTE_TYPE",
                NodeKind::Apply => "APPLY",
                NodeKind::Lambda => "LAMBDA",
                NodeKind::Tuple => "TUPLE",
                NodeKind::Program => "PROGRAM",
                NodeKind::As => "AS",
                NodeKind::AsReturn => "AS_RETURN",
                NodeKind::Parameterized => "PARAMETERIZED",
                NodeKind::ApplyOpaque => "APPLY_OPAQUE",
                NodeKind::Proof => "PROOF",
                NodeKind::Variable => "VARIABLE",
            },
            Kind::Eval(op) => op.kind_name(),
        })
    }
}

/// The kinds by their numbers in a snapshot, which are their positions in
/// the `ALL` lists.
impl SymbolKind {
    pub fn from_index(i: usize) -> Option<SymbolKind> {
        SymbolKind::ALL.get(i).copied()
    }
}

impl LitKind {
    pub fn from_index(i: usize) -> Option<LitKind> {
        LitKind::ALL.get(i).copied()
    }
}

impl NodeKind {
    pub fn from_index(i: usize) -> Option<NodeKind> {
        NodeKind::ALL.get(i).copied()
    }
}

impl EvalOp {
    pub fn from_index(i: usize) -> Option<EvalOp> {
        EvalOp::ALL.get(i).map(|&(op, _)| op)
    }
}

impl Kind {
    /// The kind as two bytes, for snapshots: the group and the kind within
    /// it, which is its position in the group's `ALL`.
    pub fn code(self) -> (u8, u8) {
        match self {
            Kind::Type => (0, 0),
            Kind::BoolType => (1, 0),
            Kind::Any => (2, 0),
            Kind::Null => (3, 0),
            Kind::Symbol(k) => (4, k as u8),
            Kind::Lit(k) => (5, k as u8),
            Kind::Node(k) => (6, k as u8),
            Kind::Eval(op) => (7, op as u8),
        }
    }

    /// The kind with the given code, if there is one.
    pub fn from_code(group: u8, sub: u8) -> Option<Kind> {
        let i = usize::from(sub);
        Some(match group {
            0..=3 if sub != 0 => return None,
            0 => Kind::Type,
            1 => Kind::BoolType,
            2 => Kind::Any,
            3 => Kind::Null,
            4 => Kind::Symbol(*SymbolKind::ALL.get(i)?),
            5 => Kind::Lit(*LitKind::ALL.get(i)?),
            6 => Kind::Node(*NodeKind::ALL.get(i)?),
            7 => Kind::Eval(EvalOp::ALL.get(i)?.0),
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eval_op_table_is_in_declaration_order() {
        for (i, (op, _)) in EvalOp::ALL.iter().enumerate() {
            assert_eq!(*op as usize, i);
        }
        assert_eq!(EvalOp::DtSelectors.name(), "dt_selectors");
        assert_eq!(Kind::Eval(EvalOp::IntDiv).to_term_string(), "eo::zdiv");
        assert_eq!(Kind::Eval(EvalOp::IntDiv).to_string(), "EVAL_INT_DIV");
    }
}

#[cfg(test)]
mod code_tests {
    use super::*;

    #[test]
    fn codes_round_trip() {
        // the position in ALL is the discriminant
        for (i, k) in SymbolKind::ALL.iter().enumerate() {
            assert_eq!(*k as usize, i);
        }
        for (i, k) in LitKind::ALL.iter().enumerate() {
            assert_eq!(*k as usize, i);
        }
        for (i, k) in NodeKind::ALL.iter().enumerate() {
            assert_eq!(*k as usize, i);
        }
        for (i, (op, _)) in EvalOp::ALL.iter().enumerate() {
            assert_eq!(*op as usize, i);
        }
        for group in 0..=8u8 {
            for sub in 0..=255u8 {
                if let Some(k) = Kind::from_code(group, sub) {
                    assert_eq!(k.code(), (group, sub));
                }
            }
        }
        assert_eq!(Kind::from_code(6, 13), None);
        assert_eq!(Kind::from_code(0, 1), None);
        assert_eq!(Kind::from_code(8, 0), None);
    }
}
