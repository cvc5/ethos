//! Fixed-width bit-vectors, as `util/bitvector.cpp` in Ethos.
//!
//! From `crates/pathos-term/src/bitvec.rs` of pathos (as of its commit
//! acae6aa); `parse` is kept for tests only.

use crate::num::Integer;

/// A bit-vector: a width and a non-negative value below `2^width`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BitVec {
    pub(crate) size: u32,
    pub(crate) value: Integer,
}

/// `2^k`, by `pow`: the bit-vector operations are written over integer
/// arithmetic, as logos defines them (`Cpc/SmtEval.lean`), so that their
/// proofs rest on the integer operations the store already uses.
fn pow2(k: u32) -> Integer {
    Integer::from(2u32).pow(k)
}

impl BitVec {
    /// The bit-vector of the given width holding `value` modulo `2^size`.
    pub fn new(size: u32, value: &Integer) -> BitVec {
        BitVec {
            size,
            value: value.mod_by_pow2(size),
        }
    }

    /// The zero bit-vector of the given width.
    pub fn zero(size: u32) -> BitVec {
        BitVec {
            size,
            value: Integer::zero(),
        }
    }

    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn value(&self) -> &Integer {
        &self.value
    }

    pub fn concat(&self, other: &BitVec) -> BitVec {
        BitVec::new(
            self.size.wrapping_add(other.size),
            &self.value.mul(&pow2(other.size)).add(&other.value),
        )
    }

    /// Bits `low ..= high`. Requires `low <= high`. The number of bits is
    /// taken modulo 2^32, as in Ethos: bits `0 ..= 2^32 - 1` are no bits.
    pub fn extract(&self, high: u32, low: u32) -> BitVec {
        let count = (high - low).wrapping_add(1);
        // `value div 2^low`, reduced modulo `2^count` by `new`
        BitVec::new(count, &self.value.euclidean_qr(&pow2(low)).0)
    }

    pub fn xor(&self, b: &BitVec) -> BitVec {
        BitVec::new(self.size, &self.value.bitwise_xor(&b.value))
    }

    pub fn or(&self, b: &BitVec) -> BitVec {
        BitVec::new(self.size, &self.value.bitwise_or(&b.value))
    }

    pub fn and(&self, b: &BitVec) -> BitVec {
        BitVec::new(self.size, &self.value.bitwise_and(&b.value))
    }

    pub fn not(&self) -> BitVec {
        // `2^size - (value + 1)`
        BitVec::new(self.size, &pow2(self.size).add(&self.value.add(&Integer::one()).neg()))
    }

    pub fn add(&self, b: &BitVec) -> BitVec {
        BitVec::new(self.size, &self.value.add(&b.value))
    }

    pub fn neg(&self) -> BitVec {
        self.not().add(&BitVec::new(self.size, &Integer::one()))
    }

    pub fn mul(&self, b: &BitVec) -> BitVec {
        BitVec::new(self.size, &self.value.mul(&b.value))
    }

    /// Unsigned division; division by zero gives all ones.
    pub fn unsigned_div_total(&self, y: &BitVec) -> BitVec {
        if y.value.sgn() == 0 {
            // Ethos builds this as 1 one-extended by size - 1 bits; for width
            // zero the count wraps around there, and the result is still
            // reduced modulo 2^0.
            // (all ones, `2^size - 1`, which is 0 for width zero)
            return BitVec::new(self.size, &pow2(self.size).add(&Integer::one().neg()));
        }
        // the values are not negative and `y` is not zero: floor division
        // is Euclidean
        BitVec::new(self.size, &self.value.euclidean_qr(&y.value).0)
    }

    /// Unsigned remainder; the remainder by zero is the dividend.
    pub fn unsigned_rem_total(&self, y: &BitVec) -> BitVec {
        if y.value.sgn() == 0 {
            return BitVec::new(self.size, &self.value);
        }
        BitVec::new(self.size, &self.value.euclidean_qr(&y.value).1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bv(s: &str) -> BitVec {
        BitVec::parse(s, 2).unwrap()
    }

    #[test]
    fn printing() {
        assert_eq!(bv("0011").to_string_base(2), "0011");
        assert_eq!(
            BitVec::parse("0f", 16).unwrap().to_string_base(2),
            "00001111"
        );
        // hexadecimal output is padded to the digits the width asks for
        assert_eq!(BitVec::parse("0f", 16).unwrap().to_string_base(16), "0f");
        assert_eq!(BitVec::zero(0).to_string_base(2), "");
    }

    /// The operations written over integer arithmetic agree with the ones
    /// they replace (the bit-level operations of `num.rs`), on every
    /// width up to 9 and every value of it, and at large widths.
    #[test]
    fn integer_forms_agree_with_the_bit_operations() {
        let one = Integer::one();
        for size in 0..=9u32 {
            for v in 0..(1u32 << size) {
                let x = BitVec::new(size, &Integer::from(v));
                assert_eq!(x.not(), BitVec::new(size, &x.value.bitwise_not()));
                let ones = if size == 0 {
                    BitVec::zero(0)
                } else {
                    BitVec::new(size, &one.one_extend(1, size - 1))
                };
                assert_eq!(x.unsigned_div_total(&BitVec::zero(size)), ones);
                for low in 0..=size {
                    for high in low..size.max(low + 1) {
                        let count = (high - low).wrapping_add(1);
                        assert_eq!(
                            x.extract(high, low),
                            BitVec::new(count, &x.value.extract_bit_range(count, low))
                        );
                    }
                }
                for w in 0..=4u32 {
                    for u in 0..(1u32 << w) {
                        let y = BitVec::new(w, &Integer::from(u));
                        assert_eq!(
                            x.concat(&y),
                            BitVec::new(
                                size + w,
                                &x.value.multiply_by_pow2(w).add(&y.value)
                            )
                        );
                        if w == size && u != 0 {
                            assert_eq!(
                                x.unsigned_div_total(&y),
                                BitVec::new(size, &x.value.floor_div_quotient(&y.value))
                            );
                            assert_eq!(
                                x.unsigned_rem_total(&y),
                                BitVec::new(size, &x.value.floor_div_remainder(&y.value))
                            );
                        }
                    }
                }
            }
        }
        // large widths
        let big = Integer::from(3u32).pow(70);
        for size in [64u32, 100, 200, 1000] {
            let x = BitVec::new(size, &big);
            assert_eq!(x.not(), BitVec::new(size, &x.value.bitwise_not()));
            assert_eq!(
                x.extract(size - 1, 7),
                BitVec::new(size - 7, &x.value.extract_bit_range(size - 7, 7))
            );
            assert_eq!(
                x.concat(&x),
                BitVec::new(2 * size, &x.value.multiply_by_pow2(size).add(&x.value))
            );
        }
    }

    #[test]
    fn arithmetic() {
        assert_eq!(bv("1111").add(&bv("0001")), bv("0000"));
        assert_eq!(bv("0001").neg(), bv("1111"));
        assert_eq!(bv("0101").not(), bv("1010"));
        assert_eq!(bv("10").concat(&bv("011")), bv("10011"));
        assert_eq!(bv("10110").extract(3, 1), bv("011"));
        // the number of bits wraps around at 2^32
        assert_eq!(bv("10110").extract(u32::MAX, 0), BitVec::zero(0));
        assert_eq!(bv("0111").unsigned_div_total(&bv("0000")), bv("1111"));
        assert_eq!(bv("0111").unsigned_rem_total(&bv("0000")), bv("0111"));
        assert_eq!(bv("0111").unsigned_div_total(&bv("0010")), bv("0011"));
    }
}
