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
    BitVec, CHECKER_STACK_SIZE, CheckError, CheckResult, Constructor, EoString, Integer, Lit,
    NUM_CODES, Rational, Store, Term, TermData, Verdict,
};
use std::fmt::{self, Write};

impl CheckError {
    /// The name of the operation or constant of `UnsupportedNative`.
    pub fn unsupported_name(&self) -> Option<&'static str> {
        match self {
            CheckError::UnsupportedNative(name) => Some(native_text(*name)),
            _ => None,
        }
    }
}
impl fmt::Debug for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CheckError::InvalidHandle => f.write_str("InvalidHandle"),
            CheckError::InvalidConstructor => f.write_str("InvalidConstructor"),
            CheckError::InvalidNative => f.write_str("InvalidNative"),
            CheckError::UnsupportedNative(name) => {
                write!(f, "UnsupportedNative({:?})", native_text(*name))
            }
            CheckError::Limit => f.write_str("Limit"),
            CheckError::Worker => f.write_str("Worker"),
        }
    }
}
impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// The text a number stands for in `CheckError::UnsupportedNative` and
/// in the calls for native constants: the generator numbers the names and
/// constants it passes to the runtime.
fn native_text(code: u32) -> &'static str {
    names::NATIVE_TEXTS.get(code as usize).copied().unwrap_or("")
}

/// A native constant as the EO definitions write it: `true`, `false`,
/// `nat.zero`, a numeral or a string literal.
#[allow(dead_code)] // A signature need not have such a constant.
pub(crate) fn native_literal(code: u32) -> CheckResult<Lit> {
    let op = native_text(code);
    Ok(if op == "true" || op == "false" {
        Lit::Boolean(op == "true")
    } else if op == "nat.zero" {
        Lit::Numeral(Integer::zero())
    } else if let Some(n) = Integer::parse(op, 10) {
        Lit::Numeral(n)
    } else if op.starts_with('"') && op.ends_with('"') && op.len() >= 2 {
        Lit::Str(EoString::parse(
            &op[1..op.len() - 1].replace("\"\"", "\""),
            true,
        ))
    } else {
        return Err(CheckError::UnsupportedNative(code));
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

// The checker's thread, and the entry points that start it.

/// Keep recursive rule code on a deliberately sized stack. Errors and worker
/// failures remain values. Resource limits are checked before recursive calls.
pub fn with_checker_stack<T: Send>(f: impl FnOnce() -> CheckResult<T> + Send) -> CheckResult<T> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(CHECKER_STACK_SIZE)
            .spawn_scoped(scope, f)
            .map_err(|_| CheckError::Worker)?
            .join()
            .map_err(|_| CheckError::Worker)?
    })
}

pub(crate) fn parse_int(s: &str) -> CheckResult<Integer> {
    Integer::parse(s, 10).ok_or(CheckError::InvalidNative)
}
pub fn parse_rat(s: &str) -> CheckResult<Rational> {
    Rational::parse(s).ok_or(CheckError::InvalidNative)
}

impl Store {
    /// Check the entire proof state machine, including typing, assumptions,
    /// step-pop, premise lookup and the final closed refutation test.
    pub fn check_refutation(&mut self, assumptions: Term, commands: Term) -> CheckResult<bool> {
        with_checker_stack(|| self.check_refutation_inner(assumptions, commands))
    }
    /// The verdict on a proof: `check_refutation` and Logos's translation
    /// side conditions.
    pub fn check_proof(&mut self, assumptions: Term, commands: Term) -> CheckResult<Verdict> {
        with_checker_stack(|| self.check_proof_inner(assumptions, commands))
    }
}

// A handle as a key of the hash maps of the program that builds the
// checker's input.
impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.0);
    }
}

// Strings, bit-vectors and literals as text.

fn is_hex_digit(c: char) -> bool {
    c.is_ascii_hexdigit()
}

/// Characters outside printable ASCII are dropped, as in Ethos, whose
/// `addCharToInternal` builds an error message for them and then discards it.
fn add_char(c: char, out: &mut Vec<u32>) {
    let code = u32::from(c);
    if (32..=127).contains(&code) {
        out.push(code);
    }
}

impl EoString {
    /// Converts text to a string. With `use_escapes`, the SMT-LIB escape
    /// sequences `폒d1d0` and `\u{d0}` to `\u{d4d3d2d1d0}` denote single
    /// code points; malformed or out-of-range sequences are kept verbatim.
    pub fn parse(s: &str, use_escapes: bool) -> EoString {
        let chars: Vec<char> = s.chars().collect();
        let mut out = Vec::with_capacity(chars.len());
        let mut i = 0;
        while i < chars.len() {
            let mut si = chars[i];
            if si != '\\' || !use_escapes {
                add_char(si, &mut out);
                i += 1;
                continue;
            }
            // The characters read so far, in case this is not an escape.
            let mut non_esc = Vec::new();
            add_char(si, &mut non_esc);
            i += 1;
            let mut is_escape = true;
            let mut hex = String::new();
            if i >= chars.len() || chars[i] != 'u' {
                is_escape = false;
            } else {
                add_char(chars[i], &mut non_esc);
                i += 1;
                let mut is_start = true;
                let mut is_end = false;
                let mut has_brace = false;
                while i < chars.len() {
                    si = chars[i];
                    if is_start {
                        is_start = false;
                        if si == '{' {
                            has_brace = true;
                            add_char(si, &mut non_esc);
                            i += 1;
                            continue;
                        }
                    } else if si == '}' {
                        // only ends an escape opened by a brace, with a digit
                        is_escape = has_brace && !hex.is_empty();
                        is_end = true;
                        add_char(si, &mut non_esc);
                        i += 1;
                        break;
                    }
                    if !is_hex_digit(si) {
                        is_escape = false;
                        break;
                    }
                    hex.push(si);
                    add_char(si, &mut non_esc);
                    i += 1;
                    if !has_brace && hex.len() == 4 {
                        is_end = true;
                        break;
                    } else if has_brace && hex.len() > 5 {
                        is_escape = false;
                        break;
                    }
                }
                if !is_end {
                    is_escape = false;
                }
            }
            if is_escape {
                match u32::from_str_radix(&hex, 16) {
                    Ok(val) if val < NUM_CODES => out.push(val),
                    _ => is_escape = false,
                }
            }
            if !is_escape {
                out.extend_from_slice(&non_esc);
            }
        }
        EoString::from_code_points(out)
    }
}

impl fmt::Display for EoString {
    /// Printable ASCII is printed as is, except the backslash; everything
    /// else is printed as `\u{<hex>}`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for &c in self.code_points() {
            if (32..=126).contains(&c) && c != u32::from(b'\\') {
                f.write_char(char::from_u32(c).unwrap_or('?'))?;
            } else {
                write!(f, "\\u{{{c:x}}}")?;
            }
        }
        Ok(())
    }
}

impl BitVec {
    /// Parses a string of binary (base 2) or hexadecimal (base 16) digits;
    /// the width follows from the number of digits. (For the tests here and
    /// in lit.rs: the compiled checker reads no bit-vector from text.)
    #[cfg(test)]
    pub fn parse(num: &str, base: u8) -> Option<BitVec> {
        let value = Integer::parse(num, base)?;
        let digits = u32::try_from(num.len()).ok()?;
        let size = if base == 16 {
            digits.checked_mul(4)?
        } else {
            digits
        };
        Some(BitVec { size, value })
    }

    /// The digits in `base`. Binary and hexadecimal output is padded to the
    /// number of digits the width asks for, so that `#x0f` and `#x00f`
    /// print differently.
    pub fn to_string_base(&self, base: u8) -> String {
        let s = self.value.to_string_base(base);
        let ndigits = match base {
            2 => self.size as usize,
            // in Ethos's 32-bit arithmetic
            16 => (self.size.wrapping_add(3) / 4) as usize,
            _ => 0,
        };
        if ndigits > s.len() {
            let mut out = "0".repeat(ndigits - s.len());
            out.push_str(&s);
            out
        } else if self.size == 0 {
            String::new()
        } else {
            s
        }
    }
}

impl fmt::Display for Lit {
    /// The text of the literal without any decoration: no `#b` prefix and no
    /// quotes. This is `Literal::toString` in Ethos.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Boolean(b) => f.write_str(if *b { "true" } else { "false" }),
            Lit::Numeral(i) => write!(f, "{i}"),
            Lit::Decimal(r) | Lit::Rational(r) => write!(f, "{r}"),
            Lit::Hex(b) => f.write_str(&b.to_string_base(16)),
            Lit::Binary(b) => f.write_str(&b.to_string_base(2)),
            Lit::Str(s) => write!(f, "{s}"),
        }
    }
}
