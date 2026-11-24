//! Literal values and the `eo::` operators on them (`literal.cpp` in Ethos).
//!
//! From `crates/pathos-term/src/lit.rs` of pathos (as of its commit
//! acae6aa), without the writing and reading of literals for snapshots,
//! which the compiled checker does not use.

use crate::bitvec::BitVec;
use crate::eostring::EoString;
use crate::MAX_CODE_POINT;
use crate::kind::{EvalOp, LitKind};
use crate::table::mix;
use crate::num::{Integer, Rational};

/// A literal value. (`Boolean` and `Str`, not `Bool` and `String`: in the
/// Lean that Aeneas writes, a variant of that name hides the type of the
/// same name in every definition about `Lit`.)
///
/// Decimal and rational literals hold the same values but are distinct terms,
/// as are hexadecimal and binary literals.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Lit {
    Boolean(bool),
    Numeral(Integer),
    Decimal(Rational),
    Rational(Rational),
    Hex(BitVec),
    Binary(BitVec),
    Str(EoString),
}

impl Lit {
    /// A hash of the literal, for the store's table of terms: equal
    /// literals have equal hashes.
    pub(crate) fn hash_code(&self) -> u64 {
        match self {
            Lit::Boolean(b) => mix(1, u64::from(*b)),
            Lit::Numeral(n) => mix(2, n.hash_code()),
            Lit::Decimal(q) => mix(3, q.hash_code()),
            Lit::Rational(q) => mix(4, q.hash_code()),
            Lit::Hex(b) => mix(mix(5, u64::from(b.size())), b.value().hash_code()),
            Lit::Binary(b) => mix(mix(6, u64::from(b.size())), b.value().hash_code()),
            Lit::Str(s) => {
                let codes = s.code_points();
                let mut h = mix(7, codes.len() as u64);
                let mut i = 0;
                while i < codes.len() {
                    h = mix(h, u64::from(codes[i]));
                    i += 1;
                }
                h
            }
        }
    }
    pub fn kind(&self) -> LitKind {
        match self {
            Lit::Boolean(_) => LitKind::Boolean,
            Lit::Numeral(_) => LitKind::Numeral,
            Lit::Decimal(_) => LitKind::Decimal,
            Lit::Rational(_) => LitKind::Rational,
            Lit::Hex(_) => LitKind::Hexadecimal,
            Lit::Binary(_) => LitKind::Binary,
            Lit::Str(_) => LitKind::Str,
        }
    }

    fn rational(which: LitKind, r: Rational) -> Lit {
        if which == LitKind::Decimal {
            Lit::Decimal(r)
        } else {
            Lit::Rational(r)
        }
    }

    fn bitvec(which: LitKind, b: BitVec) -> Lit {
        if which == LitKind::Hexadecimal {
            Lit::Hex(b)
        } else {
            Lit::Binary(b)
        }
    }

    fn as_bool(&self) -> Option<bool> {
        if let Lit::Boolean(b) = self {
            Some(*b)
        } else {
            None
        }
    }

    fn as_int(&self) -> Option<&Integer> {
        if let Lit::Numeral(i) = self {
            Some(i)
        } else {
            None
        }
    }

    fn as_rat(&self) -> Option<&Rational> {
        match self {
            Lit::Decimal(r) | Lit::Rational(r) => Some(r),
            _ => None,
        }
    }

    fn as_bv(&self) -> Option<&BitVec> {
        match self {
            Lit::Hex(b) | Lit::Binary(b) => Some(b),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&EoString> {
        if let Lit::Str(s) = self {
            Some(s)
        } else {
            None
        }
    }

    /// The `i`-th argument, if there is one.
    fn arg(args: &[Lit], i: usize) -> Option<&Lit> {
        if i < args.len() { Some(&args[i]) } else { None }
    }

    /// The `i`-th argument, if it is an integer.
    fn int_arg(args: &[Lit], i: usize) -> Option<&Integer> {
        match Lit::arg(args, i) {
            Some(a) => a.as_int(),
            None => None,
        }
    }

    /// The `i`-th argument, if it is a string.
    fn str_arg(args: &[Lit], i: usize) -> Option<&EoString> {
        match Lit::arg(args, i) {
            Some(a) => a.as_str(),
            None => None,
        }
    }

    /// Whether every argument is of the kind `ka`.
    fn all_of_kind(args: &[Lit], ka: LitKind) -> bool {
        let mut all = true;
        let mut i = 0;
        while i < args.len() {
            if args[i].kind() != ka {
                all = false;
            }
            i += 1;
        }
        all
    }

    /// Applies `op` to literal arguments. Returns `None` when the operator
    /// does not evaluate on them. The caller has checked the arity, and
    /// handles `eo::is_eq`, `eo::ite` and `eo::requires` itself.
    pub fn evaluate(op: EvalOp, args: &[Lit]) -> Option<Lit> {
        if args.is_empty() {
            return None;
        }
        let first = &args[0];
        // Most operators need all arguments to be of one kind.
        let mixed = match op {
            EvalOp::Extract | EvalOp::ToBin | EvalOp::Pow | EvalOp::Log => true,
            _ => false,
        };
        let ka = first.kind();
        if !mixed && !Lit::all_of_kind(args, ka) {
            return None;
        }
        match op {
            EvalOp::Not => Lit::evaluate_not(first, ka),
            EvalOp::And | EvalOp::Or | EvalOp::Xor | EvalOp::Add | EvalOp::Mul | EvalOp::Concat => {
                Lit::evaluate_nary(op, ka, args)
            }
            EvalOp::Neg => Lit::evaluate_neg(first, ka),
            EvalOp::Pow => Lit::evaluate_pow(first, ka, args),
            EvalOp::Log => Lit::evaluate_log(first, args),
            EvalOp::IntDiv | EvalOp::IntMod => Lit::evaluate_int_div(op, first, ka, args),
            EvalOp::RatDiv => Lit::evaluate_rat_div(first, args),
            EvalOp::IsNeg => match first {
                Lit::Numeral(i) => Some(Lit::Boolean(i.sgn() == -1)),
                Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::Boolean(rat_sgn(r) == -1)),
                _ => None,
            },
            EvalOp::Length => match first {
                Lit::Binary(b) => Some(Lit::Numeral(Integer::from(b.size()))),
                Lit::Str(s) => Some(Lit::Numeral(Integer::from(s.len()))),
                _ => None,
            },
            EvalOp::Extract => {
                let Some(i1) = Lit::int_arg(args, 1) else {
                    return None;
                };
                let Some(i2) = Lit::int_arg(args, 2) else {
                    return None;
                };
                Lit::evaluate_extract(first, i1, i2)
            }
            EvalOp::ToInt => Lit::evaluate_to_int(first),
            EvalOp::ToRat => match first {
                Lit::Rational(_) => Some(first.clone()),
                Lit::Decimal(r) => Some(Lit::Rational(r.clone())),
                Lit::Numeral(i) => Some(Lit::Rational(rat_from_integer(i))),
                _ => None,
            },
            EvalOp::ToBin => Lit::evaluate_to_bin(first, args),
            EvalOp::ToString => Lit::evaluate_to_string(first),
            EvalOp::Gt => Lit::evaluate_gt(first, args),
            EvalOp::Find => {
                let Some(s) = first.as_str() else {
                    return None;
                };
                let Some(t) = Lit::str_arg(args, 1) else {
                    return None;
                };
                Some(Lit::Numeral(match s.find(t) {
                    Some(i) => Integer::from(i),
                    None => Integer::one().neg(),
                }))
            }
            _ => None,
        }
    }

    fn evaluate_not(first: &Lit, ka: LitKind) -> Option<Lit> {
        match first {
            Lit::Boolean(b) => Some(Lit::Boolean(!*b)),
            Lit::Hex(b) | Lit::Binary(b) => Some(Lit::bitvec(ka, b.not())),
            _ => None,
        }
    }

    fn evaluate_neg(first: &Lit, ka: LitKind) -> Option<Lit> {
        match first {
            Lit::Numeral(i) => Some(Lit::Numeral(i.neg())),
            Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::rational(ka, rat_neg(r))),
            Lit::Hex(b) | Lit::Binary(b) => Some(Lit::bitvec(ka, b.neg())),
            _ => None,
        }
    }

    fn evaluate_pow(first: &Lit, ka: LitKind, args: &[Lit]) -> Option<Lit> {
        let Some(exp) = Lit::int_arg(args, 1) else {
            return None;
        };
        if !exp.fits_u32() {
            return None;
        }
        let exp = exp.to_u32();
        match first {
            Lit::Numeral(i) => Some(Lit::Numeral(i.pow(exp))),
            Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::rational(ka, rat_pow(r, exp))),
            _ => None,
        }
    }

    fn evaluate_log(first: &Lit, args: &[Lit]) -> Option<Lit> {
        let Some(base) = first.as_int() else {
            return None;
        };
        let Some(second) = Lit::arg(args, 1) else {
            return None;
        };
        let value = match second {
            Lit::Numeral(i) => i.clone(),
            Lit::Decimal(r) | Lit::Rational(r) => rat_floor(r),
            _ => return None,
        };
        Some(Lit::Numeral(integer_floor_log(base, &value)))
    }

    fn evaluate_int_div(op: EvalOp, first: &Lit, ka: LitKind, args: &[Lit]) -> Option<Lit> {
        let is_div = match op {
            EvalOp::IntDiv => true,
            _ => false,
        };
        let Some(second) = Lit::arg(args, 1) else {
            return None;
        };
        if let Lit::Numeral(n) = first {
            if let Lit::Numeral(d) = second {
                if d.sgn() == 0 {
                    return None;
                }
                let (q, r) = n.euclidean_qr(d);
                return Some(Lit::Numeral(if is_div { q } else { r }));
            }
        }
        let Some(a) = first.as_bv() else {
            return None;
        };
        let Some(b) = second.as_bv() else {
            return None;
        };
        if a.size() != b.size() {
            return None;
        }
        Some(Lit::bitvec(
            ka,
            if is_div {
                a.unsigned_div_total(b)
            } else {
                a.unsigned_rem_total(b)
            },
        ))
    }

    fn evaluate_rat_div(first: &Lit, args: &[Lit]) -> Option<Lit> {
        let Some(second) = Lit::arg(args, 1) else {
            return None;
        };
        if let Lit::Numeral(n) = first {
            if let Lit::Numeral(d) = second {
                return match Rational::from_integers(n, d) {
                    Some(q) => Some(Lit::Rational(q)),
                    None => None,
                };
            }
        }
        let Some(n) = first.as_rat() else {
            return None;
        };
        let Some(d) = second.as_rat() else {
            return None;
        };
        if rat_sgn(d) == 0 {
            return None;
        }
        Some(Lit::Rational(rat_div(n, d)))
    }

    fn evaluate_to_int(first: &Lit) -> Option<Lit> {
        match first {
            Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::Numeral(rat_floor(r))),
            Lit::Numeral(_) => Some(first.clone()),
            Lit::Binary(b) => Some(Lit::Numeral(b.value().clone())),
            // a string of length one gives its code point, or -1 for one
            // that is no character, as logos's native_str_to_code does
            // (the runtime holds none such: see `MAX_CODE_POINT`)
            Lit::Str(s) => {
                if s.len() == 1 {
                    let c = s.code_points()[0];
                    Some(Lit::Numeral(if c <= MAX_CODE_POINT {
                        Integer::from(c)
                    } else {
                        Integer::one().neg()
                    }))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn evaluate_to_bin(first: &Lit, args: &[Lit]) -> Option<Lit> {
        let Some(size) = first.as_int() else {
            return None;
        };
        if !size.fits_u32() {
            return None;
        }
        let size = size.to_u32();
        let Some(second) = Lit::arg(args, 1) else {
            return None;
        };
        match second {
            Lit::Numeral(i) => Some(Lit::Binary(BitVec::new(size, i))),
            Lit::Hex(b) | Lit::Binary(b) => Some(Lit::Binary(BitVec::new(size, b.value()))),
            _ => None,
        }
    }

    fn evaluate_to_string(first: &Lit) -> Option<Lit> {
        match first {
            // a code point gives the string of that one character
            Lit::Numeral(i) => {
                if i.fits_u32() && i.to_u32() <= MAX_CODE_POINT {
                    Some(Lit::Str(EoString::from_code_points(vec![i.to_u32()])))
                } else {
                    None
                }
            }
            Lit::Str(_) => Some(first.clone()),
            _ => None,
        }
    }

    fn evaluate_gt(first: &Lit, args: &[Lit]) -> Option<Lit> {
        let Some(second) = Lit::arg(args, 1) else {
            return None;
        };
        if let Lit::Numeral(a) = first {
            if let Lit::Numeral(b) = second {
                return Some(Lit::Boolean(a > b));
            }
        }
        if let Some(a) = first.as_rat() {
            if let Some(b) = second.as_rat() {
                return Some(Lit::Boolean(matches!(rat_cmp(a, b), std::cmp::Ordering::Greater)));
            }
        }
        let Some(a) = first.as_bv() else {
            return None;
        };
        let Some(b) = second.as_bv() else {
            return None;
        };
        // bitwise values are only compared at the same width
        if a.size() != b.size() {
            return None;
        }
        Some(Lit::Boolean(a.value() > b.value()))
    }

    /// An operator of two or more arguments, all of the kind `ka` of the
    /// first: the arguments are folded from the left.
    fn evaluate_nary(op: EvalOp, ka: LitKind, args: &[Lit]) -> Option<Lit> {
        match &args[0] {
            Lit::Boolean(b) => Lit::fold_bool(op, *b, args),
            Lit::Numeral(i) => Lit::fold_int(op, i, args),
            Lit::Decimal(r) | Lit::Rational(r) => Lit::fold_rat(op, ka, r, args),
            Lit::Hex(b) | Lit::Binary(b) => Lit::fold_bv(op, ka, b, args),
            Lit::Str(s) => Lit::fold_str(op, s, args),
        }
    }

    fn fold_bool(op: EvalOp, first: bool, args: &[Lit]) -> Option<Lit> {
        let mut res = Some(first);
        let mut i = 1;
        while i < args.len() {
            res = match res {
                Some(r) => match args[i].as_bool() {
                    Some(a) => match op {
                        EvalOp::And => Some(r && a),
                        EvalOp::Or => Some(r || a),
                        EvalOp::Xor => Some((r && !a) || (!r && a)),
                        _ => None,
                    },
                    None => None,
                },
                None => None,
            };
            i += 1;
        }
        match res {
            Some(r) => Some(Lit::Boolean(r)),
            None => None,
        }
    }

    fn fold_int(op: EvalOp, first: &Integer, args: &[Lit]) -> Option<Lit> {
        let mut res = Some(first.clone());
        let mut i = 1;
        while i < args.len() {
            res = match res {
                Some(r) => match args[i].as_int() {
                    Some(a) => match op {
                        EvalOp::Add => Some(r.add(a)),
                        EvalOp::Mul => Some(r.mul(a)),
                        _ => None,
                    },
                    None => None,
                },
                None => None,
            };
            i += 1;
        }
        match res {
            Some(r) => Some(Lit::Numeral(r)),
            None => None,
        }
    }

    fn fold_rat(op: EvalOp, ka: LitKind, first: &Rational, args: &[Lit]) -> Option<Lit> {
        let mut res = Some(first.clone());
        let mut i = 1;
        while i < args.len() {
            res = match res {
                Some(r) => match args[i].as_rat() {
                    Some(a) => match op {
                        EvalOp::Add => Some(rat_add(&r, a)),
                        EvalOp::Mul => Some(rat_mul(&r, a)),
                        _ => None,
                    },
                    None => None,
                },
                None => None,
            };
            i += 1;
        }
        match res {
            Some(r) => Some(Lit::rational(ka, r)),
            None => None,
        }
    }

    fn is_bv_of_size(&self, size: u32) -> bool {
        match self.as_bv() {
            Some(b) => b.size() == size,
            None => false,
        }
    }

    /// Whether every argument after the first is a bit-vector of `size` bits.
    fn all_of_size(args: &[Lit], size: u32) -> bool {
        let mut all = true;
        let mut i = 1;
        while i < args.len() {
            if !args[i].is_bv_of_size(size) {
                all = false;
            }
            i += 1;
        }
        all
    }

    fn fold_bv(op: EvalOp, ka: LitKind, first: &BitVec, args: &[Lit]) -> Option<Lit> {
        let concat = match op {
            EvalOp::Concat => true,
            _ => false,
        };
        if !concat && !Lit::all_of_size(args, first.size()) {
            return None;
        }
        let mut res = Some(first.clone());
        let mut i = 1;
        while i < args.len() {
            res = match res {
                Some(r) => match args[i].as_bv() {
                    Some(a) => match op {
                        EvalOp::And => Some(r.and(a)),
                        EvalOp::Or => Some(r.or(a)),
                        EvalOp::Xor => Some(r.xor(a)),
                        EvalOp::Add => Some(r.add(a)),
                        EvalOp::Mul => Some(r.mul(a)),
                        EvalOp::Concat => Some(r.concat(a)),
                        _ => None,
                    },
                    None => None,
                },
                None => None,
            };
            i += 1;
        }
        match res {
            Some(r) => Some(Lit::bitvec(ka, r)),
            None => None,
        }
    }

    fn fold_str(op: EvalOp, first: &EoString, args: &[Lit]) -> Option<Lit> {
        match op {
            EvalOp::Concat => {}
            _ => return None,
        }
        let mut res = Some(first.clone());
        let mut i = 1;
        while i < args.len() {
            res = match res {
                Some(r) => match args[i].as_str() {
                    Some(a) => Some(r.concat(a)),
                    None => None,
                },
                None => None,
            };
            i += 1;
        }
        match res {
            Some(r) => Some(Lit::Str(r)),
            None => None,
        }
    }

    /// `(eo::extract s i1 i2)`: bits or characters `i1 ..= i2`.
    fn evaluate_extract(s: &Lit, i1: &Integer, i2: &Integer) -> Option<Lit> {
        match s {
            Lit::Hex(b) | Lit::Binary(b) => {
                let ka = s.kind();
                let dsize = Integer::from(b.size());
                if i1.sgn() < 0 || i2.sgn() < 0 || *i1 >= dsize || dsize.sgn() == 0 {
                    return Some(Lit::bitvec(ka, BitVec::zero(0)));
                }
                let v1 = i1.to_u32();
                let vs = b.size();
                // the upper index is cut to the last bit, as for strings
                let v2 = if *i2 >= dsize { vs - 1 } else { i2.to_u32() };
                if v1 > v2 {
                    return Some(Lit::bitvec(ka, BitVec::zero(0)));
                }
                Some(Lit::bitvec(ka, b.extract(v2, v1)))
            }
            Lit::Str(st) => {
                let dsize = Integer::from(st.len());
                if i1.sgn() < 0 || i2.sgn() < 0 || *i1 > dsize || dsize.sgn() == 0 {
                    return Some(Lit::Str(EoString::from_code_points(Vec::new())));
                }
                let v1 = i1.to_u32() as usize;
                let vs = st.len();
                let v2 = if *i2 >= dsize {
                    vs - 1
                } else {
                    i2.to_u32() as usize
                };
                let esize = if v2 >= v1 { v2 + 1 - v1 } else { 0 };
                Some(Lit::Str(
                    st.substr(v1.min(vs), esize.min(vs - v1.min(vs))),
                ))
            }
            _ => None,
        }
    }
}

// Rational arithmetic, from a numerator and a denominator, as logos defines
// it: `from_integers`, `numerator`, `denominator` and the integer
// operations are the only rational operations the proofs trust. A
// denominator is positive and the pair reduced (`from_integers`
// normalizes), so the comparison of two rationals is that of the cross
// products, and the floor the Euclidean quotient.

/// The rational `n / d`, for `d` not zero (the `None` of `from_integers`
/// is never reached).
fn rat(n: &Integer, d: &Integer) -> Rational {
    match Rational::from_integers(n, d) {
        Some(q) => q,
        None => Rational::from_integer(&Integer::zero()),
    }
}

pub(crate) fn rat_from_integer(n: &Integer) -> Rational {
    rat(n, &Integer::one())
}

pub(crate) fn rat_add(a: &Rational, b: &Rational) -> Rational {
    rat(
        &a.numerator().mul(&b.denominator()).add(&b.numerator().mul(&a.denominator())),
        &a.denominator().mul(&b.denominator()),
    )
}

pub(crate) fn rat_mul(a: &Rational, b: &Rational) -> Rational {
    rat(&a.numerator().mul(&b.numerator()), &a.denominator().mul(&b.denominator()))
}

/// `a / b`, for `b` not zero.
pub(crate) fn rat_div(a: &Rational, b: &Rational) -> Rational {
    rat(&a.numerator().mul(&b.denominator()), &a.denominator().mul(&b.numerator()))
}

pub(crate) fn rat_neg(a: &Rational) -> Rational {
    rat(&a.numerator().neg(), &a.denominator())
}

pub(crate) fn rat_pow(a: &Rational, exp: u32) -> Rational {
    rat(&a.numerator().pow(exp), &a.denominator().pow(exp))
}

pub(crate) fn rat_sgn(a: &Rational) -> i32 {
    a.numerator().sgn()
}

pub(crate) fn rat_floor(a: &Rational) -> Integer {
    a.numerator().euclidean_qr(&a.denominator()).0
}

/// The order of two rationals: by their signs where they differ (no
/// product needed), else by cross-multiplying.
pub(crate) fn rat_cmp(a: &Rational, b: &Rational) -> std::cmp::Ordering {
    let sa = rat_sgn(a);
    let sb = rat_sgn(b);
    if sa < sb {
        return std::cmp::Ordering::Less;
    }
    if sa > sb {
        return std::cmp::Ordering::Greater;
    }
    if sa == 0 {
        return std::cmp::Ordering::Equal;
    }
    let x = a.numerator().mul(&b.denominator());
    let y = b.numerator().mul(&a.denominator());
    x.partial_cmp(&y).unwrap_or(std::cmp::Ordering::Equal)
}

/// The greatest `m >= 0` with `base^m <= value`, or 0 if `base <= 1` or
/// `value <= 0`.
fn integer_floor_log(base: &Integer, value: &Integer) -> Integer {
    let one = Integer::one();
    if *base <= one || value.sgn() <= 0 {
        return Integer::zero();
    }
    let mut result = Integer::zero();
    let mut remaining = value.clone();
    while *base <= remaining {
        result = result.add(&one);
        // (`remaining` and `base` are positive: floor division is Euclidean)
        remaining = remaining.euclidean_qr(base).0;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `eo::to_z` of a one-character string: its code point, as before, on
    /// every character; -1 past them, as logos says.
    #[test]
    fn to_z_of_a_character() {
        for c in [0u32, 65, 0xffff, MAX_CODE_POINT] {
            if c > MAX_CODE_POINT {
                continue;
            }
            let s = Lit::Str(EoString::from_code_points(vec![c]));
            assert_eq!(Lit::evaluate_to_int(&s), Some(Lit::Numeral(Integer::from(c))));
        }
        let s = Lit::Str(EoString::from_code_points(vec![MAX_CODE_POINT + 1]));
        assert_eq!(Lit::evaluate_to_int(&s), Some(Lit::Numeral(Integer::one().neg())));
    }

    /// The rational arithmetic from numerators and denominators agrees
    /// with the operations of `num.rs` it replaces.
    #[test]
    fn rational_forms_agree_with_the_rational_operations() {
        let mut qs = Vec::new();
        for n in -7i32..=7 {
            for d in 1u32..=6 {
                let n = if n < 0 {
                    Integer::from((-n) as u32).neg()
                } else {
                    Integer::from(n as u32)
                };
                qs.push(Rational::from_integers(&n, &Integer::from(d)).unwrap());
            }
        }
        let big = Integer::from(3u32).pow(50);
        qs.push(Rational::from_integers(&big, &Integer::from(7u32)).unwrap());
        qs.push(Rational::from_integers(&big.neg(), &Integer::from(11u32).pow(9)).unwrap());
        for a in &qs {
            assert_eq!(rat_neg(a), a.neg());
            assert_eq!(rat_sgn(a), a.sgn());
            assert_eq!(rat_floor(a), a.floor());
            for k in 0..4u32 {
                assert_eq!(rat_pow(a, k), a.pow(k));
            }
            for b in &qs {
                assert_eq!(rat_add(a, b), a.add(b));
                assert_eq!(rat_mul(a, b), a.mul(b));
                assert_eq!(rat_cmp(a, b), a.partial_cmp(b).unwrap());
                if b.sgn() != 0 {
                    assert_eq!(rat_div(a, b), a.div(b));
                }
            }
        }
        for n in [Integer::zero(), Integer::one(), big.clone(), big.neg()] {
            assert_eq!(rat_from_integer(&n), Rational::from_integer(&n));
        }
    }

    /// `rat_cmp` decides by the signs where they differ: every combination
    /// of signs, zero on either side, and `eo::gt` through it.
    #[test]
    fn rational_order_by_signs() {
        let big = Integer::from(3u32).pow(60);
        let mut qs = vec![Rational::from_integer(&Integer::zero())];
        for (n, d) in [(Integer::one(), Integer::from(3u32)), (big.clone(), Integer::from(7u32)),
                       (Integer::from(5u32), big.clone())] {
            qs.push(Rational::from_integers(&n, &d).unwrap());
            qs.push(Rational::from_integers(&n.neg(), &d).unwrap());
        }
        for a in &qs {
            for b in &qs {
                let order = a.partial_cmp(b).unwrap();
                assert_eq!(rat_cmp(a, b), order);
                assert_eq!(
                    Lit::evaluate(EvalOp::Gt, &[Lit::Rational(a.clone()), Lit::Rational(b.clone())]),
                    Some(Lit::Boolean(order == std::cmp::Ordering::Greater))
                );
            }
        }
    }

    fn num(s: &str) -> Lit {
        Lit::Numeral(Integer::parse(s, 10).unwrap())
    }

    fn string(s: &str) -> Lit {
        Lit::Str(EoString::parse(s, true))
    }

    fn bin(s: &str) -> Lit {
        Lit::Binary(BitVec::parse(s, 2).unwrap())
    }

    #[test]
    fn arithmetic() {
        assert_eq!(
            Lit::evaluate(EvalOp::Add, &[num("1"), num("2")]),
            Some(num("3"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::IntDiv, &[num("-7"), num("2")]),
            Some(num("-4"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::IntMod, &[num("-7"), num("2")]),
            Some(num("1"))
        );
        assert_eq!(Lit::evaluate(EvalOp::IntDiv, &[num("7"), num("0")]), None);
        assert_eq!(
            Lit::evaluate(EvalOp::IsNeg, &[num("-1")]),
            Some(Lit::Boolean(true))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Add, &[num("1"), Lit::Boolean(true)]),
            None
        );
        assert_eq!(
            Lit::evaluate(EvalOp::RatDiv, &[num("6"), num("4")])
                .unwrap()
                .to_string(),
            "3/2"
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Log, &[num("2"), num("9")]),
            Some(num("3"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Pow, &[num("2"), num("10")]),
            Some(num("1024"))
        );
    }

    #[test]
    fn strings() {
        assert_eq!(
            Lit::evaluate(EvalOp::Concat, &[string("ab"), string("c")]),
            Some(string("abc"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[string("hello"), num("1"), num("3")]),
            Some(string("ell"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[string("hello"), num("3"), num("99")]),
            Some(string("lo"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[string("hello"), num("5"), num("9")]),
            Some(string(""))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Find, &[string("abc"), string("z")]),
            Some(num("-1"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::ToInt, &[string("A")]),
            Some(num("65"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::ToString, &[num("65")]),
            Some(string("A"))
        );
    }

    #[test]
    fn bitvectors() {
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[bin("10110"), num("1"), num("3")]),
            Some(bin("011"))
        );
        // an upper index at or past the width is cut to the last bit, and
        // a lower index at the width gives the empty bit-vector
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[bin("101"), num("1"), num("3")]),
            Some(bin("10"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[bin("101"), num("3"), num("5")]),
            Some(Lit::Binary(BitVec::zero(0)))
        );
        // bit-vectors are compared only at the same width
        assert_eq!(
            Lit::evaluate(EvalOp::Gt, &[bin("10"), bin("01")]),
            Some(Lit::Boolean(true))
        );
        assert_eq!(Lit::evaluate(EvalOp::Gt, &[bin("10"), bin("001")]), None);
        assert_eq!(
            Lit::evaluate(EvalOp::ToBin, &[num("4"), num("-1")]),
            Some(bin("1111"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Length, &[bin("0000")]),
            Some(num("4"))
        );
        assert_eq!(Lit::evaluate(EvalOp::Add, &[bin("01"), bin("001")]), None);
    }
}
