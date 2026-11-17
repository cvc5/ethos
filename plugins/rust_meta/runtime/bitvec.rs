//! Fixed-width bit-vectors, as `util/bitvector.cpp` in Ethos.

use crate::num::Integer;

/// A bit-vector: a width and a non-negative value below `2^width`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BitVec {
    size: u32,
    value: Integer,
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

    /// Parses a string of binary (base 2) or hexadecimal (base 16) digits;
    /// the width follows from the number of digits.
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

    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn value(&self) -> &Integer {
        &self.value
    }

    /// The digits in `base`. Binary output is padded to the width;
    /// hexadecimal output is not, as in Ethos.
    pub fn to_string_base(&self, base: u8) -> String {
        let s = self.value.to_string_base(base);
        let size = self.size as usize;
        if base == 2 && size > s.len() {
            let mut out = "0".repeat(size - s.len());
            out.push_str(&s);
            out
        } else if self.size == 0 {
            String::new()
        } else {
            s
        }
    }

    pub fn concat(&self, other: &BitVec) -> BitVec {
        BitVec::new(
            self.size.wrapping_add(other.size),
            &self.value.multiply_by_pow2(other.size).add(&other.value),
        )
    }

    /// Bits `low ..= high`. Requires `low <= high`. The number of bits is
    /// taken modulo 2^32, as in Ethos: bits `0 ..= 2^32 - 1` are no bits.
    pub fn extract(&self, high: u32, low: u32) -> BitVec {
        let count = (high - low).wrapping_add(1);
        BitVec::new(count, &self.value.extract_bit_range(count, low))
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
        BitVec::new(self.size, &self.value.bitwise_not())
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
            if self.size == 0 {
                return BitVec::zero(0);
            }
            return BitVec::new(self.size, &Integer::one().one_extend(1, self.size - 1));
        }
        BitVec::new(self.size, &self.value.floor_div_quotient(&y.value))
    }

    /// Unsigned remainder; the remainder by zero is the dividend.
    pub fn unsigned_rem_total(&self, y: &BitVec) -> BitVec {
        if y.value.sgn() == 0 {
            return BitVec::new(self.size, &self.value);
        }
        BitVec::new(self.size, &self.value.floor_div_remainder(&y.value))
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
        // hexadecimal output is not padded
        assert_eq!(BitVec::parse("0f", 16).unwrap().to_string_base(16), "f");
        assert_eq!(BitVec::zero(0).to_string_base(2), "");
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
