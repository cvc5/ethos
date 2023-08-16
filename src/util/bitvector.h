
#ifndef BITVECTOR_H
#define BITVECTOR_H

#include <iosfwd>
#include <iostream>

#include "util/integer.h"

namespace alfc {

class BitVector
{
 public:
  BitVector(unsigned size, const Integer& val)
      : d_size(size), d_value(val.modByPow2(size))
  {
  }

  BitVector(unsigned size = 0) : d_size(size), d_value(0) {}

  /**
   * BitVector constructor using a 32-bit unsigned integer for the value.
   *
   * Note: we use an explicit bit-width here to be consistent across
   * platforms (long is 32-bit when compiling 64-bit binaries on
   * Windows but 64-bit on Linux) and to prevent ambiguous overloads.
   */
  BitVector(unsigned size, uint32_t z) : d_size(size), d_value(z)
  {
    d_value = d_value.modByPow2(size);
  }

  /**
   * BitVector constructor using a 64-bit unsigned integer for the value.
   *
   * Note: we use an explicit bit-width here to be consistent across
   * platforms (long is 32-bit when compiling 64-bit binaries on
   * Windows but 64-bit on Linux) and to prevent ambiguous overloads.
   */
  BitVector(unsigned size, uint64_t z) : d_size(size), d_value(z)
  {
    d_value = d_value.modByPow2(size);
  }

  BitVector(unsigned size, const BitVector& q)
      : d_size(size), d_value(q.d_value)
  {
  }

  /**
   * BitVector constructor.
   *
   * The value of the bit-vector is passed in as string of base 2, 10 or 16.
   * The size of resulting bit-vector is
   * - base  2: the size of the binary string
   * - base 10: the min. size required to represent the decimal as a bit-vector
   * - base 16: the max. size required to represent the hexadecimal as a
   *            bit-vector (4 * size of the given value string)
   *
   * @param num The value of the bit-vector in string representation.
   *            This cannot be a negative value.
   * @param base The base of the string representation.
   */
  BitVector(const std::string& num, uint32_t base = 2);

  ~BitVector() {}

  BitVector& operator=(const BitVector& x)
  {
    if (this == &x) return *this;
    d_size = x.d_size;
    d_value = x.d_value;
    return *this;
  }

  /* Get size (bit-width). */
  unsigned getSize() const;
  /* Get value. */
  const Integer& getValue() const;

  /* Return value. */
  Integer toInteger() const;
  /* Return Integer corresponding to two's complement interpretation of this. */
  Integer toSignedInteger() const;
  /* Return (binary) string representation. */
  std::string toString(unsigned int base = 2) const;

  /**
   * Set bit at index 'i' to given value.
   * Returns a reference to this bit-vector to allow for chaining.
   *
   * value: True to set bit to 1, and false to set it to 0.
   *
   * Note: Least significant bit is at index 0.
   */
  BitVector& setBit(uint32_t i, bool value);

  /** Return true if bit at index 'i' is 1, and false otherwise. */
  bool isBitSet(uint32_t i) const;

  /* Return k if the value of this is equal to 2^{k-1}, and zero otherwise. */
  unsigned isPow2() const;

  /* -----------------------------------------------------------------------
   ** Operators
   * ----------------------------------------------------------------------- */

  /* String Operations ----------------------------------------------------- */

  /* Return the concatenation of this and bit-vector 'other'. */
  BitVector concat(const BitVector& other) const;

  /* Return the bit range from index 'high' to index 'low'. */
  BitVector extract(unsigned high, unsigned low) const;

  /* Unsigned Inequality --------------------------------------------------- */

  /* Return true if this is unsigned less than bit-vector 'y'.
   * This function is a synonym for operator < but performs additional
   * argument checks.*/
  bool unsignedLessThan(const BitVector& y) const;

  /* Return true if this is unsigned less than or equal to bit-vector 'y'.
   * This function is a synonym for operator >= but performs additional
   * argument checks.*/
  bool unsignedLessThanEq(const BitVector& y) const;

  /* Signed Inequality ----------------------------------------------------- */

  /* Return true if this is signed less than bit-vector 'y'. */
  bool signedLessThan(const BitVector& y) const;

  /* Return true if this is signed less than or equal to bit-vector 'y'. */
  bool signedLessThanEq(const BitVector& y) const;

  /* Arithmetic operations ------------------------------------------------- */

  /* Total division function.
   * Returns a bit-vector representing 2^d_size-1 (signed: -1) when the
   * denominator is zero, and a bit-vector representing the unsigned division
   * (this / y), otherwise.  */
  BitVector unsignedDivTotal(const BitVector& y) const;

  /* Total remainder function.
   * Returns this when the denominator is zero, and the unsigned remainder
   * (this % y), otherwise.  */
  BitVector unsignedRemTotal(const BitVector& y) const;

  /* Extend operations ----------------------------------------------------- */

  /* Return a bit-vector representing this extended by 'n' zero bits. */
  BitVector zeroExtend(unsigned n) const;

  /* Return a bit-vector representing this extended by 'n' bits of the value
   * of the signed bit. */
  BitVector signExtend(unsigned n) const;

  /* Shift operations ------------------------------------------------------ */

  /* Return a bit-vector representing a left shift of this by 'y'. */
  BitVector leftShift(const BitVector& y) const;

  /* Return a bit-vector representing a logical right shift of this by 'y'. */
  BitVector logicalRightShift(const BitVector& y) const;

  /* Return a bit-vector representing an arithmetic right shift of this
   * by 'y'.*/
  BitVector arithRightShift(const BitVector& y) const;

  /* -----------------------------------------------------------------------
   ** Static helpers.
   * ----------------------------------------------------------------------- */

  /* Create zero bit-vector of given size. */
  static BitVector mkZero(unsigned size);

  /* Create bit-vector representing value 1 of given size. */
  static BitVector mkOne(unsigned size);

  /* Create bit-vector of ones of given size. */
  static BitVector mkOnes(unsigned size);

  /* Create bit-vector representing the minimum signed value of given size. */
  static BitVector mkMinSigned(unsigned size);

  /* Create bit-vector representing the maximum signed value of given size. */
  static BitVector mkMaxSigned(unsigned size);

 private:
  /**
   * Class invariants:
   *  - no overflows: 2^d_size < d_value
   *  - no negative numbers: d_value >= 0
   */

  unsigned d_size;
  Integer d_value;

}; /* class BitVector */

/* (Dis)Equality --------------------------------------------------------- */

/**
 * @return True if bit-vector `a` is equal to bit-vector `b`.
 */
bool operator==(const BitVector& a, const BitVector& b);

/* Bit-wise operations --------------------------------------------------- */

/**
 * @return A bit-vector representing the bit-wise xor of bit-vectors `a`
 *         and `b`.
 */
BitVector operator^(const BitVector& a, const BitVector& b);

/**
 * @return A bit-vector representing the bit-wise or of bit-vectors `a`
 *         and `b`.
 */
BitVector operator|(const BitVector& a, const BitVector& b);

/**
 * @return A bit-vector representing the bit-wise and of bit-vectors `a`
 *         and `b`.
 */
BitVector operator&(const BitVector& a, const BitVector& b);

/**
 * @return A bit-vector representing the bit-wise not of bit-vector `a`.
 */
BitVector operator~(const BitVector& a);

/* Arithmetic operations ------------------------------------------------- */

/**
 * @return A bit-vector representing the addition of bit-vectors `a` and `b`.
 */
BitVector operator+(const BitVector& a, const BitVector& b);

/**
 * @return A bit-vector representing the negation of bit-vector `a`.
 */
BitVector operator-(const BitVector& a);

/**
 * @return A bit-vector representing the multiplication of bit-vectors `a`
 *         and `b`.
 */
BitVector operator*(const BitVector& a, const BitVector& b);


}  // namespace cvc5::internal

#endif /* CVC5__BITVECTOR_H */
