//! Arbitrary-precision integers and rationals.
//!
//! From `crates/pathos-term/src/num.rs` of pathos (as of its commit
//! acae6aa), without what the compiled checker does not use
//! (`Integer::length`, `Rational::from_decimal`, `Rational::is_integral`),
//! and with `hash_code` added.
//!
//! These wrap `malachite` so the library can be swapped (design decision 9).
//! Every operation mirrors what Ethos does with GMP in `util/integer.cpp` and
//! `util/rational.h`, including rounding directions.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use malachite_base::num::arithmetic::traits::{DivMod, Floor, ModPowerOf2, Pow, Sign};
use malachite_base::num::basic::traits::{One, Zero};
use malachite_base::num::conversion::traits::{FromStringBase, ToStringBase};
use malachite_nz::integer::Integer as MInt;
use malachite_q::Rational as MRat;

/// A cheap multiply-rotate hash for `hash_code`: the hash only says where a
/// search of the store's table of terms starts, and the search compares the
/// numbers, so SipHash's protection against chosen collisions is not needed.
#[derive(Default, Clone, Copy)]
struct TermHasher(u64);
impl std::hash::Hasher for TermHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        let (chunks, rest) = bytes.as_chunks::<8>();
        for c in chunks {
            self.add(u64::from_le_bytes(*c));
        }
        for &b in rest {
            self.add(u64::from(b));
        }
    }
    fn write_u8(&mut self, i: u8) {
        self.add(u64::from(i))
    }
    fn write_u32(&mut self, i: u32) {
        self.add(u64::from(i))
    }
    fn write_u64(&mut self, i: u64) {
        self.add(i)
    }
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64)
    }
}
impl TermHasher {
    #[inline]
    fn add(&mut self, w: u64) {
        self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

/// An arbitrary-precision integer.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Integer(MInt);

impl Integer {
    /// A hash of the number: equal numbers have equal hashes.
    pub fn hash_code(&self) -> u64 {
        let mut h = TermHasher::default();
        self.0.hash(&mut h);
        h.finish()
    }

    pub fn zero() -> Integer {
        Integer(MInt::ZERO)
    }

    pub fn one() -> Integer {
        Integer(MInt::ONE)
    }

    /// Parses an optionally negated string of digits in `base` (2, 10 or 16).
    /// Returns `None` where GMP would reject the string.
    pub fn parse(s: &str, base: u8) -> Option<Integer> {
        if s.is_empty() || s == "-" {
            return None;
        }
        MInt::from_string_base(base, s).map(Integer)
    }

    /// The sign: -1, 0 or 1.
    pub fn sgn(&self) -> i32 {
        match self.0.sign() {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }

    pub fn neg(&self) -> Integer {
        Integer(-&self.0)
    }

    pub fn add(&self, y: &Integer) -> Integer {
        Integer(&self.0 + &y.0)
    }

    pub fn mul(&self, y: &Integer) -> Integer {
        Integer(&self.0 * &y.0)
    }

    pub fn pow(&self, exp: u32) -> Integer {
        Integer((&self.0).pow(u64::from(exp)))
    }

    pub fn bitwise_or(&self, y: &Integer) -> Integer {
        Integer(&self.0 | &y.0)
    }

    pub fn bitwise_and(&self, y: &Integer) -> Integer {
        Integer(&self.0 & &y.0)
    }

    pub fn bitwise_xor(&self, y: &Integer) -> Integer {
        Integer(&self.0 ^ &y.0)
    }

    /// Two's complement negation of all bits, as `mpz_com`.
    pub fn bitwise_not(&self) -> Integer {
        Integer(!&self.0)
    }

    pub fn multiply_by_pow2(&self, pow: u32) -> Integer {
        Integer(&self.0 << u64::from(pow))
    }

    /// The remainder of the floor division by `2^exp`; never negative.
    pub fn mod_by_pow2(&self, exp: u32) -> Integer {
        Integer(MInt::from((&self.0).mod_power_of_2(u64::from(exp))))
    }

    /// Bits `low .. low + bit_count` of the value, as a non-negative integer.
    pub fn extract_bit_range(&self, bit_count: u32, low: u32) -> Integer {
        let high = u64::from(low) + u64::from(bit_count);
        let rem = MInt::from((&self.0).mod_power_of_2(high));
        Integer(rem >> u64::from(low))
    }

    /// The value `2^amount - 1` shifted left by `size`, or-ed into `self`.
    pub fn one_extend(&self, size: u32, amount: u32) -> Integer {
        let ones = (MInt::ONE << u64::from(amount)) - MInt::ONE;
        Integer(&self.0 | (ones << u64::from(size)))
    }

    /// The quotient rounded towards negative infinity. `y` must be non-zero.
    pub fn floor_div_quotient(&self, y: &Integer) -> Integer {
        Integer((&self.0).div_mod(&y.0).0)
    }

    /// The remainder of the floor division. `y` must be non-zero.
    pub fn floor_div_remainder(&self, y: &Integer) -> Integer {
        Integer((&self.0).div_mod(&y.0).1)
    }

    /// Euclidean division: the remainder is never negative. `y` must be
    /// non-zero.
    pub fn euclidean_qr(&self, y: &Integer) -> (Integer, Integer) {
        let (mut q, mut r) = (&self.0).div_mod(&y.0);
        // The floor remainder is negative only when `y` is negative.
        if r.sign() == Ordering::Less {
            q += MInt::ONE;
            r -= &y.0;
        }
        (Integer(q), Integer(r))
    }

    pub fn fits_u32(&self) -> bool {
        u32::try_from(&self.0).is_ok()
    }

    /// The value as a `u32`. Meaningful only when [`Integer::fits_u32`].
    pub fn to_u32(&self) -> u32 {
        u32::try_from(&self.0).unwrap_or(0)
    }

    pub fn to_string_base(&self, base: u8) -> String {
        self.0.to_string_base(base)
    }
}

impl From<u32> for Integer {
    fn from(v: u32) -> Integer {
        Integer(MInt::from(v))
    }
}

impl From<u64> for Integer {
    fn from(v: u64) -> Integer {
        Integer(MInt::from(v))
    }
}

impl From<usize> for Integer {
    fn from(v: usize) -> Integer {
        Integer(MInt::from(v))
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An arbitrary-precision rational, always in lowest terms.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Rational(MRat);

impl Rational {
    /// A hash of the number: equal numbers have equal hashes.
    pub fn hash_code(&self) -> u64 {
        let mut h = TermHasher::default();
        self.0.hash(&mut h);
        h.finish()
    }

    /// `n / d`, or `None` when `d` is zero.
    pub fn from_integers(n: &Integer, d: &Integer) -> Option<Rational> {
        if d.sgn() == 0 {
            return None;
        }
        Some(Rational(MRat::from_integers_ref(&n.0, &d.0)))
    }

    /// The numerator of the number in lowest terms, with its sign.
    pub fn numerator(&self) -> Integer {
        let n = MInt::from(self.0.numerator_ref());
        Integer(if self.0.sign() == Ordering::Less { -n } else { n })
    }

    /// The denominator of the number in lowest terms, which is positive.
    pub fn denominator(&self) -> Integer {
        Integer(MInt::from(self.0.denominator_ref()))
    }

    pub fn from_integer(n: &Integer) -> Rational {
        Rational(MRat::from(&n.0))
    }

    /// Parses `<integer>` or `<integer>/<integer>`.
    pub fn parse(s: &str) -> Option<Rational> {
        match s.split_once('/') {
            Some((n, d)) => {
                Rational::from_integers(&Integer::parse(n, 10)?, &Integer::parse(d, 10)?)
            }
            None => Some(Rational::from_integer(&Integer::parse(s, 10)?)),
        }
    }

    pub fn sgn(&self) -> i32 {
        match self.0.sign() {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }

    pub fn floor(&self) -> Integer {
        Integer((&self.0).floor())
    }

    pub fn neg(&self) -> Rational {
        Rational(-&self.0)
    }

    pub fn add(&self, y: &Rational) -> Rational {
        Rational(&self.0 + &y.0)
    }

    pub fn mul(&self, y: &Rational) -> Rational {
        Rational(&self.0 * &y.0)
    }

    /// `self / y`. `y` must be non-zero.
    pub fn div(&self, y: &Rational) -> Rational {
        Rational(&self.0 / &y.0)
    }

    pub fn pow(&self, exp: u32) -> Rational {
        Rational((&self.0).pow(u64::from(exp)))
    }

}

impl fmt::Display for Rational {
    /// Prints `n/d`, with the denominator even when it is 1, as Ethos does.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.sign() == Ordering::Less {
            f.write_str("-")?;
        }
        write!(f, "{}/{}", self.0.numerator_ref(), self.0.denominator_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(s: &str) -> Integer {
        Integer::parse(s, 10).unwrap()
    }

    #[test]
    fn parse_and_print() {
        assert_eq!(int("-0012").to_string(), "-12");
        assert_eq!(Integer::parse("ff", 16).unwrap().to_string(), "255");
        assert_eq!(Integer::parse("FF", 16).unwrap().to_string_base(16), "ff");
        assert!(Integer::parse("", 10).is_none());
        assert!(Integer::parse("1a", 10).is_none());
    }

    #[test]
    fn division_matches_gmp() {
        // floor division, as mpz_fdiv_q / mpz_fdiv_r
        assert_eq!(int("-7").floor_div_quotient(&int("2")), int("-4"));
        assert_eq!(int("-7").floor_div_remainder(&int("2")), int("1"));
        assert_eq!(int("7").floor_div_quotient(&int("-2")), int("-4"));
        assert_eq!(int("7").floor_div_remainder(&int("-2")), int("-1"));
        // Euclidean division: the remainder is never negative
        for (x, y, q, r) in [
            ("7", "2", "3", "1"),
            ("-7", "2", "-4", "1"),
            ("7", "-2", "-3", "1"),
            ("-7", "-2", "4", "1"),
            ("6", "-3", "-2", "0"),
        ] {
            assert_eq!(int(x).euclidean_qr(&int(y)), (int(q), int(r)), "{x} / {y}");
        }
    }

    #[test]
    fn bits() {
        assert_eq!(int("-1").mod_by_pow2(4), int("15"));
        assert_eq!(int("5").bitwise_not(), int("-6"));
        assert_eq!(int("182").extract_bit_range(3, 2), int("5"));
        assert_eq!(int("1").one_extend(1, 3), int("15"));
        assert!(int("4294967295").fits_u32());
        assert!(!int("4294967296").fits_u32());
        assert!(!int("-1").fits_u32());
    }

    #[test]
    fn rationals() {
        assert_eq!(Rational::parse("6/4").unwrap().to_string(), "3/2");
        assert_eq!(Rational::parse("-6/3").unwrap().to_string(), "-2/1");
        assert_eq!(Rational::parse("5").unwrap().to_string(), "5/1");
        assert!(Rational::parse("1/0").is_none());
        assert_eq!(Rational::parse("-7/2").unwrap().floor(), int("-4"));
        assert_eq!(Rational::parse("7/2").unwrap().floor(), int("3"));
        assert_eq!(Rational::parse("2/3").unwrap().pow(2).to_string(), "4/9");
    }
}
