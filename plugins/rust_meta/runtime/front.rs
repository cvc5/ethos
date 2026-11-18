//! The part of the runtime that works on text: the names of constructors
//! and operations, the reading of constants written as text, and the
//! printing of errors. It is for the program that builds the checker's
//! input and reports its result, and it is the one part of this crate that
//! is not meant to be translated for verification. The checking functions
//! take from it only pure functions from text to values
//! ([`native_literal`], [`constant_name`]).

#[path = "names.rs"]
mod names;

use crate::{
    CheckError, CheckResult, Constructor, EoString, EvalOp, Integer, Lit, NUM_CODES, Rational,
    Store, Term, TermData,
};
use std::fmt;

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// A native constant as the EO definitions write it: `true`, `false`,
/// `nat.zero`, a numeral or a string literal.
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

    // The entry points by name that generated code used before it named
    // operations by `NativeOp` and `EvalOp`.

    /// Match the only native algebraic constructors (Nat.zero/succ), or
    /// a native literal. Arithmetic functions are never used as patterns.
    pub(crate) fn native_pattern(&mut self, op: &'static str, t: Term) -> CheckResult<Option<Vec<Term>>> {
        if op == "nat.succ" {
            let n = self.raw_int(t)?;
            return if n.sgn() > 0 {
                Ok(Some(vec![
                    self.raw(Lit::Numeral(n.add(&Integer::one().neg())))?,
                ]))
            } else {
                Ok(None)
            };
        }
        let expected = self.native(op, &[])?;
        Ok((expected == t).then(Vec::new))
    }

    pub(crate) fn native(&mut self, op: &'static str, a: &[Term]) -> CheckResult<Term> {
        if a.is_empty() {
            let lit = if op == "true" || op == "false" {
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
            };
            return self.raw(lit);
        }
        match (op, a) {
            ("teq" | "Teq", &[x, y]) => return self.raw(Lit::Bool(x == y)),
            ("tcmp", &[x, y]) => return self.raw(Lit::Bool(self.compare(x, y)?.is_lt())),
            ("is_ok", &[x]) => return self.raw(Lit::Bool(!self.is_stuck(x)?)),
            ("not", &[x]) => {
                let Some(b) = self.boolean_value(x, true)? else {
                    return Err(CheckError::InvalidNative);
                };
                return self.raw(Lit::Bool(!b));
            }
            ("and" | "or" | "iff", &[x, y]) => {
                let (Some(x), Some(y)) =
                    (self.boolean_value(x, true)?, self.boolean_value(y, true)?)
                else {
                    return Err(CheckError::InvalidNative);
                };
                return self.raw(Lit::Bool(match op {
                    "and" => x && y,
                    "or" => x || y,
                    _ => x == y,
                }));
            }
            ("nat.succ", &[x]) => {
                return self.raw(Lit::Numeral(self.raw_int(x)?.add(&Integer::one())));
            }
            ("nat.pred", &[x]) => {
                let n = self.raw_int(x)?;
                return self.raw(Lit::Numeral(if n.sgn() > 0 {
                    n.add(&Integer::one().neg())
                } else {
                    Integer::zero()
                }));
            }
            ("nat.to_int" | "Int.ofNat", &[x]) => {
                self.raw_int(x)?;
                return Ok(x);
            }
            ("int.to_nat" | "Int.toNat", &[x]) => {
                let n = self.raw_int(x)?;
                return self.raw(Lit::Numeral(if n.sgn() < 0 { Integer::zero() } else { n }));
            }
            ("zeq" | "nateq" | "zlt" | "zleq" | "nat.lt", &[x, y]) => {
                let (x, y) = (self.raw_int(x)?, self.raw_int(y)?);
                return self.raw(Lit::Bool(match op {
                    "zeq" | "nateq" => x == y,
                    "zleq" => x <= y,
                    _ => x < y,
                }));
            }
            (
                "zplus" | "zmult" | "zdiv_total" | "div_total" | "mod_total" | "zmod_total"
                | "zexp_total" | "binary_and" | "binary_or" | "binary_xor",
                &[x, y],
            ) => {
                let (x, y) = (self.raw_int(x)?, self.raw_int(y)?);
                let n = match op {
                    "zplus" => x.add(&y),
                    "zmult" => x.mul(&y),
                    "binary_and" => x.bitwise_and(&y),
                    "binary_or" => x.bitwise_or(&y),
                    "binary_xor" => x.bitwise_xor(&y),
                    "zexp_total" => {
                        if y.sgn() < 0 {
                            Integer::zero()
                        } else if y.fits_u32() {
                            x.pow(y.to_u32())
                        } else {
                            return Err(CheckError::Limit);
                        }
                    }
                    _ if y.sgn() == 0 => {
                        if op == "zmod_total" || op == "mod_total" {
                            x
                        } else {
                            Integer::zero()
                        }
                    }
                    "zdiv_total" | "div_total" => x.euclidean_qr(&y).0,
                    _ => x.euclidean_qr(&y).1,
                };
                return self.raw(Lit::Numeral(n));
            }
            ("zneg" | "zabs", &[x]) => {
                let x = self.raw_int(x)?;
                return self.raw(Lit::Numeral(if op == "zneg" || x.sgn() < 0 {
                    x.neg()
                } else {
                    x
                }));
            }
            ("qeq" | "qlt" | "qleq", &[x, y]) => {
                let (x, y) = (self.raw_rat(x)?, self.raw_rat(y)?);
                return self.raw(Lit::Bool(match op {
                    "qeq" => x == y,
                    "qleq" => x <= y,
                    _ => x < y,
                }));
            }
            ("qplus" | "qmult" | "qdiv_total", &[x, y]) => {
                let (x, y) = (self.raw_rat(x)?, self.raw_rat(y)?);
                return self.raw(Lit::Rational(match op {
                    "qplus" => x.add(&y),
                    "qmult" => x.mul(&y),
                    _ if y.sgn() == 0 => Rational::from_integer(&Integer::zero()),
                    _ => x.div(&y),
                }));
            }
            ("qneg" | "qabs", &[x]) => {
                let x = self.raw_rat(x)?;
                return self.raw(Lit::Rational(if op == "qneg" || x.sgn() < 0 {
                    x.neg()
                } else {
                    x
                }));
            }
            ("mk_rational", &[n, d]) => {
                let q = Rational::from_integers(&self.raw_int(n)?, &self.raw_int(d)?)
                    .ok_or(CheckError::InvalidNative)?;
                return self.raw(Lit::Rational(q));
            }
            ("to_int", &[x]) => return self.raw(Lit::Numeral(self.raw_rat(x)?.floor())),
            ("to_real", &[x]) => {
                return self.raw(Lit::Rational(Rational::from_integer(&self.raw_int(x)?)));
            }
            ("streq", &[x, y]) => return self.raw(Lit::Bool(self.view(x)? == self.view(y)?)),
            ("int.pow2", &[x]) => {
                let n = self.raw_int(x)?;
                if n.sgn() < 0 {
                    return self.raw(Lit::Numeral(Integer::zero()));
                }
                if !n.fits_u32() {
                    return Err(CheckError::Limit);
                }
                return self.raw(Lit::Numeral(Integer::from(2u32).pow(n.to_u32())));
            }
            ("uconst_id" | "const_id", &[x]) => {
                let n = self.raw_int(x)?;
                if n.sgn() < 0 {
                    return Err(CheckError::InvalidNative);
                }
                let prefix = if op == "uconst_id" { "@u." } else { "@c." };
                return self.raw(Lit::String(EoString::parse(&format!("{prefix}{n}"), false)));
            }
            ("string_valid", &[x]) => {
                let TermData::Native(Lit::String(s)) = self.view(x)? else {
                    return Err(CheckError::InvalidNative);
                };
                return self.raw(Lit::Bool(s.code_points().iter().all(|&c| c < NUM_CODES)));
            }
            ("string_prefix_eq", &[x, y]) => {
                let (TermData::Native(Lit::String(x)), TermData::Native(Lit::String(y))) =
                    (self.view(x)?, self.view(y)?)
                else {
                    return Err(CheckError::InvalidNative);
                };
                return self.raw(Lit::Bool(y.code_points().starts_with(x.code_points())));
            }
            _ => {}
        }
        Err(CheckError::UnsupportedNative(op))
    }

    pub(crate) fn operator(&mut self, name: &'static str, args: &[Term]) -> CheckResult<Term> {
        let op = EvalOp::ALL
            .iter()
            .find_map(|&(op, n)| (n == name).then_some(op))
            .ok_or_else(|| CheckError::UnsupportedNative(name))?;
        self.builtin(op, args)
    }
}
