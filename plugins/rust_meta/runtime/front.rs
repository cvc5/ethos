//! The part of the runtime that works on text: the names of constructors
//! and operations, the reading of constants written as text, and the
//! printing of errors. It is for the program that builds the checker's
//! input and reports its result, and it is the one part of this crate that
//! is not meant to be translated for verification. The checking functions
//! take from it only pure functions from text to values
//! ([`native_literal`], [`constant_name`]).

#[path = "names.rs"]
mod names;

use crate::{CheckError, CheckResult, Constructor, EoString, Integer, Lit, Store, Term, TermData};
use std::fmt;

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// A native constant as the EO definitions write it: `true`, `false`,
/// `nat.zero`, a numeral or a string literal.
#[allow(dead_code)] // A signature need not have such a constant.
pub(crate) fn native_literal(op: &'static str) -> CheckResult<Lit> {
    Ok(if op == "true" || op == "false" {
        Lit::Bool(op == "true")
    } else if op == "nat.zero" {
        Lit::Numeral(Integer::zero())
    } else if let Some(n) = Integer::parse(op, 10) {
        Lit::Numeral(n)
    } else if op.starts_with('"') && op.ends_with('"') && op.len() >= 2 {
        Lit::String(EoString::parse(
            &op[1..op.len() - 1].replace("\"\"", "\""),
            true,
        ))
    } else {
        return Err(CheckError::UnsupportedNative(op));
    })
}

/// The name of the `n`-th constant: `@u.n` of an uninterpreted sort
/// (`uninterpreted`), `@c.n` otherwise.
pub(crate) fn constant_name(uninterpreted: bool, n: &Integer) -> EoString {
    let prefix = if uninterpreted { "@u." } else { "@c." };
    EoString::parse(&format!("{prefix}{n}"), false)
}

impl Store {
    pub fn is_named(&self, t: Term, name: &str) -> CheckResult<bool> {
        Ok(match self.view(t)? {
            TermData::Node(c, _) => c.name() == name,
            _ => false,
        })
    }
    pub fn named(&mut self, name: &str, args: &[Term]) -> CheckResult<Term> {
        let c = Constructor::from_name(name).ok_or(CheckError::InvalidConstructor)?;
        self.construct(c, args)
    }
}
