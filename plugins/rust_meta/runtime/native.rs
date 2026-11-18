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
    /// not take.
    pub(crate) fn unsupported_native(&mut self, name: &'static str) -> CheckResult<Term> {
        Err(CheckError::UnsupportedNative(name))
    }
    /// What generated code calls in the place of a constructor of the
    /// embedding that the signature does not have.
    pub(crate) fn missing_constructor(&mut self) -> CheckResult<Term> {
        Err(CheckError::InvalidConstructor)
    }
    /// The native boolean `b`.
    pub(crate) fn native_bool(&mut self, b: bool) -> CheckResult<Term> {
        self.raw(Lit::Bool(b))
    }
    /// The native natural number zero.
    pub(crate) fn native_nat_zero(&mut self) -> CheckResult<Term> {
        self.raw(Lit::Numeral(Integer::zero()))
    }
    /// Another native constant, written as in the EO definitions: a
    /// numeral or a string literal.
    pub(crate) fn native_constant(&mut self, text: &'static str) -> CheckResult<Term> {
        let lit = crate::front::native_literal(text)?;
        self.raw(lit)
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
        text: &'static str,
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
        self.native_bool(order.is_lt())
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
            NativeOp::Qleq => x <= y,
            _ => x < y,
        })
    }
    fn native_rat_binary(&mut self, op: NativeOp, x: Term, y: Term) -> CheckResult<Term> {
        let x = self.raw_rat(x)?;
        let y = self.raw_rat(y)?;
        self.raw(Lit::Rational(match op {
            NativeOp::Qplus => x.add(&y),
            NativeOp::Qmult => x.mul(&y),
            // QdivTotal
            _ => {
                if y.sgn() == 0 {
                    Rational::from_integer(&Integer::zero())
                } else {
                    x.div(&y)
                }
            }
        }))
    }
    fn native_rat_unary(&mut self, op: NativeOp, x: Term) -> CheckResult<Term> {
        let x = self.raw_rat(x)?;
        self.raw(Lit::Rational(if op == NativeOp::Qneg || x.sgn() < 0 {
            x.neg()
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
        self.raw(Lit::Numeral(q.floor()))
    }
    fn native_to_real(&mut self, x: Term) -> CheckResult<Term> {
        let n = self.raw_int(x)?;
        self.raw(Lit::Rational(Rational::from_integer(&n)))
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
        let name = crate::front::constant_name(op == NativeOp::UconstId, &n);
        self.raw(Lit::String(name))
    }
    fn native_string(&self, x: Term) -> CheckResult<&EoString> {
        match self.view(x)? {
            TermData::Native(Lit::String(s)) => Ok(s),
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
        let (TermData::Native(Lit::String(x)), TermData::Native(Lit::String(y))) =
            (self.view(x)?, self.view(y)?)
        else {
            return Err(CheckError::InvalidNative);
        };
        let (x, y) = (x.code_points(), y.code_points());
        let mut prefix = x.len() <= y.len();
        let mut i = 0;
        while prefix && i < x.len() {
            if x[i] != y[i] {
                prefix = false;
            }
            i += 1;
        }
        self.native_bool(prefix)
    }
}
