//! The native operations of the embedding: the functions on native
//! booleans, naturals, integers, rationals and strings that the generated
//! code calls where the EO definitions use `$native_apply_*`.
//!
//! An operation is named by a [`NativeOp`], which the generator writes at
//! each call from the operation's name; no text is compared here. The
//! generator checks the number of arguments of each call, so a call with
//! another number is a mistake of the caller (`InvalidNative`).

use crate::{
    CheckError, CheckResult, EoString, Integer, Lit, NUM_CODES, Rational, Store, Term, TermData,
};
use crate::lit::{rat_add, rat_cmp, rat_div, rat_floor, rat_from_integer, rat_mul, rat_neg, rat_sgn};

/// A native operation with arguments. `Teq` is also `teq`, `NatToInt` also
/// `Int.ofNat`, `IntToNat` also `Int.toNat`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum NativeOp {
    Teq,
    Tcmp,
    IsOk,
    Not,
    And,
    Or,
    Iff,
    NatSucc,
    NatPred,
    NatToInt,
    IntToNat,
    Zeq,
    Nateq,
    Zlt,
    Zleq,
    NatLt,
    Zplus,
    Zmult,
    ZdivTotal,
    DivTotal,
    ModTotal,
    ZmodTotal,
    ZexpTotal,
    BinaryAnd,
    BinaryOr,
    BinaryXor,
    Zneg,
    Zabs,
    Qeq,
    Qlt,
    Qleq,
    Qplus,
    Qmult,
    QdivTotal,
    Qneg,
    Qabs,
    MkRational,
    ToInt,
    ToReal,
    Streq,
    IntPow2,
    UconstId,
    ConstId,
    StringValid,
    StringPrefixEq,
}

impl NativeOp {
    /// The number of arguments of the operation.
    pub fn arity(self) -> usize {
        match self {
            NativeOp::IsOk
            | NativeOp::Not
            | NativeOp::NatSucc
            | NativeOp::NatPred
            | NativeOp::NatToInt
            | NativeOp::IntToNat
            | NativeOp::Zneg
            | NativeOp::Zabs
            | NativeOp::Qneg
            | NativeOp::Qabs
            | NativeOp::ToInt
            | NativeOp::ToReal
            | NativeOp::IntPow2
            | NativeOp::UconstId
            | NativeOp::ConstId
            | NativeOp::StringValid => 1,
            _ => 2,
        }
    }
}

impl Store {
    /// What generated code calls in the place of an operation whose name
    /// the runtime does not have, or with a number of arguments it does
    /// not take. `name` stands for the name (see `CheckError`).
    pub(crate) fn unsupported_native(&mut self, name: u32) -> CheckResult<Term> {
        Err(CheckError::UnsupportedNative(name))
    }
    /// What generated code calls in the place of a constructor of the
    /// embedding that the signature does not have.
    pub(crate) fn missing_constructor(&mut self) -> CheckResult<Term> {
        Err(CheckError::InvalidConstructor)
    }
    /// The native boolean `b`.
    pub(crate) fn native_bool(&mut self, b: bool) -> CheckResult<Term> {
        self.raw(Lit::Boolean(b))
    }
    /// The native natural number zero.
    pub(crate) fn native_nat_zero(&mut self) -> CheckResult<Term> {
        self.raw(Lit::Numeral(Integer::zero()))
    }
    /// Another native constant: generated code builds Booleans, `nat.zero`,
    /// numerals and string literals as values, so the runtime refuses any
    /// other. `text` stands for what is written (see `CheckError`).
    pub(crate) fn native_constant(&mut self, text: u32) -> CheckResult<Term> {
        Err(CheckError::UnsupportedNative(text))
    }

    /// Match the only native algebraic constructors (Nat.zero/succ), or
    /// a native literal. Arithmetic functions are never used as patterns.
    pub(crate) fn native_pattern_succ(&mut self, t: Term) -> CheckResult<Option<Vec<Term>>> {
        let n = self.raw_int(t)?;
        if n.sgn() > 0 {
            let pred = self.raw(Lit::Numeral(n.add(&Integer::one().neg())))?;
            Ok(Some(vec![pred]))
        } else {
            Ok(None)
        }
    }
    pub(crate) fn native_pattern_bool(
        &mut self,
        b: bool,
        t: Term,
    ) -> CheckResult<Option<Vec<Term>>> {
        let expected = self.native_bool(b)?;
        Ok(Self::pattern_constant(expected, t))
    }
    pub(crate) fn native_pattern_nat_zero(&mut self, t: Term) -> CheckResult<Option<Vec<Term>>> {
        let expected = self.native_nat_zero()?;
        Ok(Self::pattern_constant(expected, t))
    }
    pub(crate) fn native_pattern_constant(
        &mut self,
        text: u32,
        t: Term,
    ) -> CheckResult<Option<Vec<Term>>> {
        let expected = self.native_constant(text)?;
        Ok(Self::pattern_constant(expected, t))
    }
    fn pattern_constant(expected: Term, t: Term) -> Option<Vec<Term>> {
        if expected == t { Some(Vec::new()) } else { None }
    }

    /// The call `(op a...)`, on native values.
    pub(crate) fn native_op(&mut self, op: NativeOp, a: &[Term]) -> CheckResult<Term> {
        if a.len() != op.arity() {
            return Err(CheckError::InvalidNative);
        }
        let x = a[0];
        match op {
            NativeOp::Teq => self.native_bool(x == a[1]),
            NativeOp::Tcmp => self.native_tcmp(x, a[1]),
            NativeOp::IsOk => self.native_is_ok(x),
            NativeOp::Not => self.native_not(x),
            NativeOp::And | NativeOp::Or | NativeOp::Iff => self.native_connective(op, x, a[1]),
            NativeOp::NatSucc => self.native_succ(x),
            NativeOp::NatPred => self.native_pred(x),
            NativeOp::NatToInt => self.native_nat_to_int(x),
            NativeOp::IntToNat => self.native_int_to_nat(x),
            NativeOp::Zeq | NativeOp::Nateq | NativeOp::Zlt | NativeOp::Zleq | NativeOp::NatLt => {
                self.native_int_compare(op, x, a[1])
            }
            NativeOp::Zplus
            | NativeOp::Zmult
            | NativeOp::ZdivTotal
            | NativeOp::DivTotal
            | NativeOp::ModTotal
            | NativeOp::ZmodTotal
            | NativeOp::ZexpTotal
            | NativeOp::BinaryAnd
            | NativeOp::BinaryOr
            | NativeOp::BinaryXor => self.native_int_binary(op, x, a[1]),
            NativeOp::Zneg | NativeOp::Zabs => self.native_int_unary(op, x),
            NativeOp::Qeq | NativeOp::Qlt | NativeOp::Qleq => self.native_rat_compare(op, x, a[1]),
            NativeOp::Qplus | NativeOp::Qmult | NativeOp::QdivTotal => {
                self.native_rat_binary(op, x, a[1])
            }
            NativeOp::Qneg | NativeOp::Qabs => self.native_rat_unary(op, x),
            NativeOp::MkRational => self.native_mk_rational(x, a[1]),
            NativeOp::ToInt => self.native_to_int(x),
            NativeOp::ToReal => self.native_to_real(x),
            NativeOp::Streq => self.native_streq(x, a[1]),
            NativeOp::IntPow2 => self.native_pow2(x),
            NativeOp::UconstId | NativeOp::ConstId => self.native_const_id(op, x),
            NativeOp::StringValid => self.native_string_valid(x),
            NativeOp::StringPrefixEq => self.native_string_prefix_eq(x, a[1]),
        }
    }

    fn native_tcmp(&mut self, x: Term, y: Term) -> CheckResult<Term> {
        let order = self.compare(x, y)?;
        self.native_bool(is_less(order))
    }
    fn native_is_ok(&mut self, x: Term) -> CheckResult<Term> {
        let stuck = self.is_stuck(x)?;
        self.native_bool(!stuck)
    }
    fn native_bool_value(&self, x: Term) -> CheckResult<bool> {
        match self.boolean_value(x, true)? {
            Some(b) => Ok(b),
            None => Err(CheckError::InvalidNative),
        }
    }
    fn native_not(&mut self, x: Term) -> CheckResult<Term> {
        let b = self.native_bool_value(x)?;
        self.native_bool(!b)
    }
    fn native_connective(&mut self, op: NativeOp, x: Term, y: Term) -> CheckResult<Term> {
        // Both values are read before either is refused.
        let x = self.boolean_value(x, true)?;
        let y = self.boolean_value(y, true)?;
        let (Some(x), Some(y)) = (x, y) else {
            return Err(CheckError::InvalidNative);
        };
        self.native_bool(match op {
            NativeOp::And => x && y,
            NativeOp::Or => x || y,
            _ => x == y,
        })
    }
    fn native_succ(&mut self, x: Term) -> CheckResult<Term> {
        let n = self.raw_int(x)?;
        self.raw(Lit::Numeral(n.add(&Integer::one())))
    }
    fn native_pred(&mut self, x: Term) -> CheckResult<Term> {
        let n = self.raw_int(x)?;
        self.raw(Lit::Numeral(if n.sgn() > 0 {
            n.add(&Integer::one().neg())
        } else {
            Integer::zero()
        }))
    }
    fn native_nat_to_int(&mut self, x: Term) -> CheckResult<Term> {
        self.raw_int(x)?;
        Ok(x)
    }
    fn native_int_to_nat(&mut self, x: Term) -> CheckResult<Term> {
        let n = self.raw_int(x)?;
        self.raw(Lit::Numeral(if n.sgn() < 0 { Integer::zero() } else { n }))
    }
    fn native_int_compare(&mut self, op: NativeOp, x: Term, y: Term) -> CheckResult<Term> {
        let x = self.raw_int(x)?;
        let y = self.raw_int(y)?;
        self.native_bool(match op {
            NativeOp::Zeq | NativeOp::Nateq => x == y,
            NativeOp::Zleq => x <= y,
            _ => x < y,
        })
    }
    fn native_int_binary(&mut self, op: NativeOp, x: Term, y: Term) -> CheckResult<Term> {
        let x = self.raw_int(x)?;
        let y = self.raw_int(y)?;
        let n = match op {
            NativeOp::Zplus => x.add(&y),
            NativeOp::Zmult => x.mul(&y),
            NativeOp::BinaryAnd => x.bitwise_and(&y),
            NativeOp::BinaryOr => x.bitwise_or(&y),
            NativeOp::BinaryXor => x.bitwise_xor(&y),
            NativeOp::ZexpTotal => {
                if y.sgn() < 0 {
                    Integer::zero()
                } else if y.fits_u32() {
                    x.pow(y.to_u32())
                } else {
                    return Err(CheckError::Limit);
                }
            }
            NativeOp::ZdivTotal | NativeOp::DivTotal => {
                if y.sgn() == 0 {
                    Integer::zero()
                } else {
                    x.euclidean_qr(&y).0
                }
            }
            // ZmodTotal, ModTotal
            _ => {
                if y.sgn() == 0 {
                    x
                } else {
                    x.euclidean_qr(&y).1
                }
            }
        };
        self.raw(Lit::Numeral(n))
    }
    fn native_int_unary(&mut self, op: NativeOp, x: Term) -> CheckResult<Term> {
        let x = self.raw_int(x)?;
        self.raw(Lit::Numeral(if op == NativeOp::Zneg || x.sgn() < 0 {
            x.neg()
        } else {
            x
        }))
    }
    fn native_rat_compare(&mut self, op: NativeOp, x: Term, y: Term) -> CheckResult<Term> {
        let x = self.raw_rat(x)?;
        let y = self.raw_rat(y)?;
        self.native_bool(match op {
            NativeOp::Qeq => x == y,
            NativeOp::Qleq => !matches!(rat_cmp(&x, &y), std::cmp::Ordering::Greater),
            _ => matches!(rat_cmp(&x, &y), std::cmp::Ordering::Less),
        })
    }
    fn native_rat_binary(&mut self, op: NativeOp, x: Term, y: Term) -> CheckResult<Term> {
        let x = self.raw_rat(x)?;
        let y = self.raw_rat(y)?;
        self.raw(Lit::Rational(match op {
            NativeOp::Qplus => rat_add(&x, &y),
            NativeOp::Qmult => rat_mul(&x, &y),
            // QdivTotal
            _ => {
                if rat_sgn(&y) == 0 {
                    rat_from_integer(&Integer::zero())
                } else {
                    rat_div(&x, &y)
                }
            }
        }))
    }
    fn native_rat_unary(&mut self, op: NativeOp, x: Term) -> CheckResult<Term> {
        let x = self.raw_rat(x)?;
        self.raw(Lit::Rational(if op == NativeOp::Qneg || rat_sgn(&x) < 0 {
            rat_neg(&x)
        } else {
            x
        }))
    }
    fn native_mk_rational(&mut self, n: Term, d: Term) -> CheckResult<Term> {
        let n = self.raw_int(n)?;
        let d = self.raw_int(d)?;
        match Rational::from_integers(&n, &d) {
            Some(q) => self.raw(Lit::Rational(q)),
            None => Err(CheckError::InvalidNative),
        }
    }
    fn native_to_int(&mut self, x: Term) -> CheckResult<Term> {
        let q = self.raw_rat(x)?;
        self.raw(Lit::Numeral(rat_floor(&q)))
    }
    fn native_to_real(&mut self, x: Term) -> CheckResult<Term> {
        let n = self.raw_int(x)?;
        self.raw(Lit::Rational(rat_from_integer(&n)))
    }
    /// Whether two terms have the same data. Every term is interned, so two
    /// handles of the store have the same data exactly when they are the
    /// same handle.
    fn native_streq(&mut self, x: Term, y: Term) -> CheckResult<Term> {
        self.view(x)?;
        self.view(y)?;
        self.native_bool(x == y)
    }
    fn native_pow2(&mut self, x: Term) -> CheckResult<Term> {
        let n = self.raw_int(x)?;
        if n.sgn() < 0 {
            return self.raw(Lit::Numeral(Integer::zero()));
        }
        if !n.fits_u32() {
            return Err(CheckError::Limit);
        }
        self.raw(Lit::Numeral(Integer::from(2u32).pow(n.to_u32())))
    }
    fn native_const_id(&mut self, op: NativeOp, x: Term) -> CheckResult<Term> {
        let n = self.raw_int(x)?;
        if n.sgn() < 0 {
            return Err(CheckError::InvalidNative);
        }
        let name = constant_name(op == NativeOp::UconstId, &n)?;
        self.raw(Lit::Str(name))
    }
    fn native_string(&self, x: Term) -> CheckResult<&EoString> {
        match self.view(x)? {
            TermData::Native(Lit::Str(s)) => Ok(s),
            _ => Err(CheckError::InvalidNative),
        }
    }
    fn native_string_valid(&mut self, x: Term) -> CheckResult<Term> {
        let codes = self.native_string(x)?.code_points();
        let mut valid = true;
        let mut i = 0;
        while i < codes.len() {
            if codes[i] >= NUM_CODES {
                valid = false;
            }
            i += 1;
        }
        self.native_bool(valid)
    }
    fn native_string_prefix_eq(&mut self, x: Term, y: Term) -> CheckResult<Term> {
        // Both strings are read before either is refused.
        self.view(x)?;
        self.view(y)?;
        let x = self.native_string(x)?;
        let y = self.native_string(y)?;
        let prefix = is_prefix(x.code_points(), y.code_points());
        self.native_bool(prefix)
    }
}

/// Whether an order is "less".
pub(crate) fn is_less(order: std::cmp::Ordering) -> bool {
    match order {
        std::cmp::Ordering::Less => true,
        _ => false,
    }
}

/// Whether `y` begins with `x`.
fn is_prefix(x: &[u32], y: &[u32]) -> bool {
    if x.len() > y.len() {
        return false;
    }
    let mut prefix = true;
    let mut i = 0;
    while i < x.len() {
        if x[i] != y[i] {
            prefix = false;
        }
        i += 1;
    }
    prefix
}

/// The most digits a constant's name may have. The name is the prefix and
/// the digits, in a vector of code points; the bound keeps every push in
/// range, and a number with more digits could not be held in memory.
const MAX_NAME_DIGITS: usize = usize::MAX - 8;

/// The name of the `n`-th constant: `@u.n` of an uninterpreted sort
/// (`uninterpreted`), `@c.n` otherwise, with `n` in decimal and a `-` before
/// a negative one (the checker asks only for `n >= 0`). This is what
/// `format!("{prefix}{n}")` writes, built from the digits so that its
/// translation can be proved to spell it.
pub(crate) fn constant_name(uninterpreted: bool, n: &Integer) -> CheckResult<EoString> {
    let kind: u32 = if uninterpreted { 117 } else { 99 };
    let negative = n.sgn() < 0;
    let m = if negative { n.neg() } else { n.clone() };
    let digits = decimal_digits(&m)?;
    let mut codes: Vec<u32> = Vec::new();
    codes.push(64);
    codes.push(kind);
    codes.push(46);
    if negative {
        codes.push(45);
    }
    let mut i = digits.len();
    while i > 0 {
        i -= 1;
        codes.push(digits[i]);
    }
    Ok(EoString::from_code_points(codes))
}

/// The decimal digits of `m >= 0` as code points, the last first.
fn decimal_digits(m: &Integer) -> CheckResult<Vec<u32>> {
    let ten = Integer::from(10u32);
    let mut digits: Vec<u32> = Vec::new();
    let mut m = m.clone();
    loop {
        if digits.len() >= MAX_NAME_DIGITS {
            return Err(CheckError::Limit);
        }
        let (q, r) = m.euclidean_qr(&ten);
        digits.push(48 + r.to_u32());
        if q.sgn() == 0 {
            return Ok(digits);
        }
        m = q;
    }
}

#[cfg(test)]
mod tests {
    use super::constant_name;
    use crate::{EoString, Integer};

    /// The name is what `format!` of the number writes, for both prefixes.
    #[test]
    fn constant_names_are_the_decimal_numbers() {
        let big = Integer::parse("123456789012345678901234567890", 10).unwrap();
        let mut values: Vec<Integer> = (0u32..1100).map(Integer::from).collect();
        values.push(Integer::from(u32::MAX));
        values.push(big.clone());
        values.push(big.neg());
        values.push(Integer::from(7u32).neg());
        for n in &values {
            for (uninterpreted, prefix) in [(true, "@u."), (false, "@c.")] {
                let expected = EoString::parse(&format!("{prefix}{n}"), false);
                assert_eq!(constant_name(uninterpreted, n), Ok(expected), "{prefix}{n}");
            }
        }
    }
}
