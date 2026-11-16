//! Literal values and the `eo::` operators on them (`literal.cpp` in Ethos).

use std::fmt;

use crate::bitvec::BitVec;
use crate::eostring::{EoString, NUM_CODES};
use crate::kind::{EvalOp, LitKind};
use crate::num::{Integer, Rational};

/// A literal value.
///
/// Decimal and rational literals hold the same values but are distinct terms,
/// as are hexadecimal and binary literals.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Lit {
    Bool(bool),
    Numeral(Integer),
    Decimal(Rational),
    Rational(Rational),
    Hex(BitVec),
    Binary(BitVec),
    String(EoString),
}

impl Lit {
    pub fn kind(&self) -> LitKind {
        match self {
            Lit::Bool(_) => LitKind::Boolean,
            Lit::Numeral(_) => LitKind::Numeral,
            Lit::Decimal(_) => LitKind::Decimal,
            Lit::Rational(_) => LitKind::Rational,
            Lit::Hex(_) => LitKind::Hexadecimal,
            Lit::Binary(_) => LitKind::Binary,
            Lit::String(_) => LitKind::String,
        }
    }

    fn rational(kind: LitKind, r: Rational) -> Lit {
        if kind == LitKind::Decimal {
            Lit::Decimal(r)
        } else {
            Lit::Rational(r)
        }
    }

    fn bitvec(kind: LitKind, b: BitVec) -> Lit {
        if kind == LitKind::Hexadecimal {
            Lit::Hex(b)
        } else {
            Lit::Binary(b)
        }
    }

    fn as_bool(&self) -> Option<bool> {
        if let Lit::Bool(b) = self {
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
        if let Lit::String(s) = self {
            Some(s)
        } else {
            None
        }
    }

    /// Applies `op` to literal arguments. Returns `None` when the operator
    /// does not evaluate on them. The caller has checked the arity, and
    /// handles `eo::is_eq`, `eo::ite` and `eo::requires` itself.
    pub fn evaluate(op: EvalOp, args: &[&Lit]) -> Option<Lit> {
        let first = *args.first()?;
        // Most operators need all arguments to be of one kind.
        let mixed = matches!(
            op,
            EvalOp::Extract | EvalOp::ToBin | EvalOp::Pow | EvalOp::Log
        );
        let ka = first.kind();
        if !mixed && args.iter().any(|a| a.kind() != ka) {
            return None;
        }
        match op {
            EvalOp::Not => match first {
                Lit::Bool(b) => Some(Lit::Bool(!b)),
                Lit::Hex(b) | Lit::Binary(b) => Some(Lit::bitvec(ka, b.not())),
                _ => None,
            },
            EvalOp::And | EvalOp::Or | EvalOp::Xor | EvalOp::Add | EvalOp::Mul | EvalOp::Concat => {
                Lit::evaluate_nary(op, ka, args)
            }
            EvalOp::Neg => match first {
                Lit::Numeral(i) => Some(Lit::Numeral(i.neg())),
                Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::rational(ka, r.neg())),
                Lit::Hex(b) | Lit::Binary(b) => Some(Lit::bitvec(ka, b.neg())),
                _ => None,
            },
            EvalOp::Pow => {
                let exp = args.get(1)?.as_int().filter(|e| e.fits_u32())?.to_u32();
                match first {
                    Lit::Numeral(i) => Some(Lit::Numeral(i.pow(exp))),
                    Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::rational(ka, r.pow(exp))),
                    _ => None,
                }
            }
            EvalOp::Log => {
                let base = first.as_int()?;
                let value = match args.get(1)? {
                    Lit::Numeral(i) => i.clone(),
                    Lit::Decimal(r) | Lit::Rational(r) => r.floor(),
                    _ => return None,
                };
                Some(Lit::Numeral(integer_floor_log(base, &value)))
            }
            EvalOp::IntDiv | EvalOp::IntMod => {
                let is_div = op == EvalOp::IntDiv;
                let second = *args.get(1)?;
                match (first, second) {
                    (Lit::Numeral(n), Lit::Numeral(d)) => {
                        if d.sgn() == 0 {
                            return None;
                        }
                        let (q, r) = n.euclidean_qr(d);
                        Some(Lit::Numeral(if is_div { q } else { r }))
                    }
                    _ => {
                        let (a, b) = (first.as_bv()?, second.as_bv()?);
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
                }
            }
            EvalOp::RatDiv => {
                let second = *args.get(1)?;
                match (first, second) {
                    (Lit::Numeral(n), Lit::Numeral(d)) => {
                        Rational::from_integers(n, d).map(Lit::Rational)
                    }
                    _ => {
                        let (n, d) = (first.as_rat()?, second.as_rat()?);
                        if d.sgn() == 0 {
                            return None;
                        }
                        Some(Lit::Rational(n.div(d)))
                    }
                }
            }
            EvalOp::IsNeg => match first {
                Lit::Numeral(i) => Some(Lit::Bool(i.sgn() == -1)),
                Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::Bool(r.sgn() == -1)),
                _ => None,
            },
            EvalOp::Length => match first {
                Lit::Binary(b) => Some(Lit::Numeral(Integer::from(b.size()))),
                Lit::String(s) => Some(Lit::Numeral(Integer::from(s.len()))),
                _ => None,
            },
            EvalOp::Extract => {
                let i1 = args.get(1)?.as_int()?;
                let i2 = args.get(2)?.as_int()?;
                Lit::evaluate_extract(first, i1, i2)
            }
            EvalOp::ToInt => match first {
                Lit::Decimal(r) | Lit::Rational(r) => Some(Lit::Numeral(r.floor())),
                Lit::Numeral(_) => Some(first.clone()),
                Lit::Binary(b) => Some(Lit::Numeral(b.value().clone())),
                // a string of length one gives its code point
                Lit::String(s) if s.len() == 1 => {
                    Some(Lit::Numeral(Integer::from(s.code_points()[0])))
                }
                _ => None,
            },
            EvalOp::ToRat => match first {
                Lit::Rational(_) => Some(first.clone()),
                Lit::Decimal(r) => Some(Lit::Rational(r.clone())),
                Lit::Numeral(i) => Some(Lit::Rational(Rational::from_integer(i))),
                _ => None,
            },
            EvalOp::ToBin => {
                let size = first.as_int().filter(|s| s.fits_u32())?.to_u32();
                match args.get(1)? {
                    Lit::Numeral(i) => Some(Lit::Binary(BitVec::new(size, i))),
                    Lit::Hex(b) | Lit::Binary(b) => Some(Lit::Binary(BitVec::new(size, b.value()))),
                    _ => None,
                }
            }
            EvalOp::ToString => match first {
                // a code point gives the string of that one character
                Lit::Numeral(i) if i.fits_u32() && i.to_u32() < NUM_CODES => {
                    Some(Lit::String(EoString::from_code_points(vec![i.to_u32()])))
                }
                Lit::String(_) => Some(first.clone()),
                _ => None,
            },
            EvalOp::Gt => {
                let second = *args.get(1)?;
                match (first, second) {
                    (Lit::Numeral(a), Lit::Numeral(b)) => Some(Lit::Bool(a > b)),
                    _ => {
                        if let (Some(a), Some(b)) = (first.as_rat(), second.as_rat()) {
                            return Some(Lit::Bool(a > b));
                        }
                        let (a, b) = (first.as_bv()?, second.as_bv()?);
                        Some(Lit::Bool(a.value() > b.value()))
                    }
                }
            }
            EvalOp::Find => {
                let (s, t) = (first.as_str()?, args.get(1)?.as_str()?);
                Some(Lit::Numeral(match s.find(t) {
                    Some(i) => Integer::from(i),
                    None => Integer::one().neg(),
                }))
            }
            _ => None,
        }
    }

    fn evaluate_nary(op: EvalOp, ka: LitKind, args: &[&Lit]) -> Option<Lit> {
        let rest = &args[1..];
        match args[0] {
            Lit::Bool(b) => {
                let mut res = *b;
                for a in rest {
                    let a = a.as_bool()?;
                    res = match op {
                        EvalOp::And => res && a,
                        EvalOp::Or => res || a,
                        EvalOp::Xor => res != a,
                        _ => return None,
                    };
                }
                Some(Lit::Bool(res))
            }
            Lit::Numeral(i) => {
                let mut res = i.clone();
                for a in rest {
                    let a = a.as_int()?;
                    res = match op {
                        EvalOp::Add => res.add(a),
                        EvalOp::Mul => res.mul(a),
                        _ => return None,
                    };
                }
                Some(Lit::Numeral(res))
            }
            Lit::Decimal(r) | Lit::Rational(r) => {
                let mut res = r.clone();
                for a in rest {
                    let a = a.as_rat()?;
                    res = match op {
                        EvalOp::Add => res.add(a),
                        EvalOp::Mul => res.mul(a),
                        _ => return None,
                    };
                }
                Some(Lit::rational(ka, res))
            }
            Lit::Hex(b) | Lit::Binary(b) => {
                if op != EvalOp::Concat
                    && rest
                        .iter()
                        .any(|a| a.as_bv().map(BitVec::size) != Some(b.size()))
                {
                    return None;
                }
                let mut res = b.clone();
                for a in rest {
                    let a = a.as_bv()?;
                    res = match op {
                        EvalOp::And => res.and(a),
                        EvalOp::Or => res.or(a),
                        EvalOp::Xor => res.xor(a),
                        EvalOp::Add => res.add(a),
                        EvalOp::Mul => res.mul(a),
                        EvalOp::Concat => res.concat(a),
                        _ => return None,
                    };
                }
                Some(Lit::bitvec(ka, res))
            }
            Lit::String(s) => {
                if op != EvalOp::Concat {
                    return None;
                }
                let mut res = s.clone();
                for a in rest {
                    res = res.concat(a.as_str()?);
                }
                Some(Lit::String(res))
            }
        }
    }

    /// `(eo::extract s i1 i2)`: bits or characters `i1 ..= i2`.
    fn evaluate_extract(s: &Lit, i1: &Integer, i2: &Integer) -> Option<Lit> {
        match s {
            Lit::Hex(b) | Lit::Binary(b) => {
                let ka = s.kind();
                let dsize = Integer::from(b.size());
                if i1.sgn() < 0 || i2.sgn() < 0 || *i1 > dsize || dsize.sgn() == 0 {
                    return Some(Lit::bitvec(ka, BitVec::zero(0)));
                }
                let v1 = i1.to_u32();
                let vs = b.size();
                let v2 = if *i2 > dsize { vs - 1 } else { i2.to_u32() };
                if v1 > v2 {
                    return Some(Lit::bitvec(ka, BitVec::zero(0)));
                }
                // Ethos reads past the width when v2 == size; the bits there
                // are zero, so extracting them from the value is the same.
                Some(Lit::bitvec(ka, b.extract(v2, v1)))
            }
            Lit::String(st) => {
                let dsize = Integer::from(st.len());
                if i1.sgn() < 0 || i2.sgn() < 0 || *i1 > dsize || dsize.sgn() == 0 {
                    return Some(Lit::String(EoString::default()));
                }
                let v1 = i1.to_u32() as usize;
                let vs = st.len();
                let v2 = if *i2 >= dsize {
                    vs - 1
                } else {
                    i2.to_u32() as usize
                };
                let esize = if v2 >= v1 { v2 + 1 - v1 } else { 0 };
                Some(Lit::String(
                    st.substr(v1.min(vs), esize.min(vs - v1.min(vs))),
                ))
            }
            _ => None,
        }
    }
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
        remaining = remaining.floor_div_quotient(base);
    }
    result
}

impl fmt::Display for Lit {
    /// The text of the literal without any decoration: no `#b` prefix and no
    /// quotes. This is `Literal::toString` in Ethos.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Bool(b) => f.write_str(if *b { "true" } else { "false" }),
            Lit::Numeral(i) => write!(f, "{i}"),
            Lit::Decimal(r) | Lit::Rational(r) => write!(f, "{r}"),
            Lit::Hex(b) => f.write_str(&b.to_string_base(16)),
            Lit::Binary(b) => f.write_str(&b.to_string_base(2)),
            Lit::String(s) => write!(f, "{s}"),
        }
    }
}

impl Lit {
    /// Writes the value, for snapshots.
    pub fn write_to(&self, w: &mut crate::codec::Writer) {
        w.u8(self.kind() as u8);
        match self {
            Lit::Bool(b) => w.bool(*b),
            Lit::Numeral(i) => w.str(&i.to_string()),
            Lit::Decimal(q) | Lit::Rational(q) => w.str(&q.to_string()),
            Lit::Hex(bv) | Lit::Binary(bv) => {
                w.u32(bv.size());
                w.str(&bv.value().to_string());
            }
            Lit::String(s) => {
                w.len(s.len());
                for &c in s.code_points() {
                    w.u32(c);
                }
            }
        }
    }

    /// Reads a value written by [`Lit::write_to`]. `None` if the input is
    /// not one.
    pub fn read_from(r: &mut crate::codec::Reader) -> Option<Lit> {
        let kind = LitKind::from_index(r.u8()? as usize)?;
        Some(match kind {
            LitKind::Boolean => Lit::Bool(r.bool()?),
            LitKind::Numeral => Lit::Numeral(Integer::parse(r.str()?, 10)?),
            LitKind::Decimal => Lit::Decimal(Rational::parse(r.str()?)?),
            LitKind::Rational => Lit::Rational(Rational::parse(r.str()?)?),
            LitKind::Hexadecimal | LitKind::Binary => {
                let size = r.u32()?;
                let value = Integer::parse(r.str()?, 10)?;
                // a value that does not fit the width is not one we wrote
                if value.sgn() < 0 || (value.sgn() > 0 && value.length() > u64::from(size)) {
                    return None;
                }
                let bv = BitVec::new(size, &value);
                if kind == LitKind::Binary {
                    Lit::Binary(bv)
                } else {
                    Lit::Hex(bv)
                }
            }
            LitKind::String => {
                let n = r.len(4)?;
                let mut codes = Vec::with_capacity(n);
                for _ in 0..n {
                    let c = r.u32()?;
                    if c >= crate::NUM_CODES {
                        return None;
                    }
                    codes.push(c);
                }
                Lit::String(EoString::from_code_points(codes))
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn num(s: &str) -> Lit {
        Lit::Numeral(Integer::parse(s, 10).unwrap())
    }

    fn string(s: &str) -> Lit {
        Lit::String(EoString::parse(s, true))
    }

    fn bin(s: &str) -> Lit {
        Lit::Binary(BitVec::parse(s, 2).unwrap())
    }

    #[test]
    fn arithmetic() {
        assert_eq!(
            Lit::evaluate(EvalOp::Add, &[&num("1"), &num("2")]),
            Some(num("3"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::IntDiv, &[&num("-7"), &num("2")]),
            Some(num("-4"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::IntMod, &[&num("-7"), &num("2")]),
            Some(num("1"))
        );
        assert_eq!(Lit::evaluate(EvalOp::IntDiv, &[&num("7"), &num("0")]), None);
        assert_eq!(
            Lit::evaluate(EvalOp::IsNeg, &[&num("-1")]),
            Some(Lit::Bool(true))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Add, &[&num("1"), &Lit::Bool(true)]),
            None
        );
        assert_eq!(
            Lit::evaluate(EvalOp::RatDiv, &[&num("6"), &num("4")])
                .unwrap()
                .to_string(),
            "3/2"
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Log, &[&num("2"), &num("9")]),
            Some(num("3"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Pow, &[&num("2"), &num("10")]),
            Some(num("1024"))
        );
    }

    #[test]
    fn strings() {
        assert_eq!(
            Lit::evaluate(EvalOp::Concat, &[&string("ab"), &string("c")]),
            Some(string("abc"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[&string("hello"), &num("1"), &num("3")]),
            Some(string("ell"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[&string("hello"), &num("3"), &num("99")]),
            Some(string("lo"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[&string("hello"), &num("5"), &num("9")]),
            Some(string(""))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Find, &[&string("abc"), &string("z")]),
            Some(num("-1"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::ToInt, &[&string("A")]),
            Some(num("65"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::ToString, &[&num("65")]),
            Some(string("A"))
        );
    }

    #[test]
    fn bitvectors() {
        assert_eq!(
            Lit::evaluate(EvalOp::Extract, &[&bin("10110"), &num("1"), &num("3")]),
            Some(bin("011"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::ToBin, &[&num("4"), &num("-1")]),
            Some(bin("1111"))
        );
        assert_eq!(
            Lit::evaluate(EvalOp::Length, &[&bin("0000")]),
            Some(num("4"))
        );
        assert_eq!(Lit::evaluate(EvalOp::Add, &[&bin("01"), &bin("001")]), None);
    }
}
