#ifndef INTEGER_H
#define INTEGER_H

#include <gmpxx.h>

#include <iosfwd>
#include <string>
#include <cstdint>

namespace alfc {

class Rational;

class Integer
{
  friend class Rational;

 public:
  /**
   * Constructs an Integer by copying a GMP C++ primitive.
   */
  Integer(const mpz_class& val) : d_value(val) {}

  /** Constructs a rational with the value 0. */
  Integer() : d_value(0) {}

  /**
   * Constructs a Integer from a C string.
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  explicit Integer(const std::string& s, unsigned base = 10);

  explicit Integer(unsigned int z) : d_value(z) {}
  Integer(const Integer& q) : d_value(q.d_value) {}

  /** Destructor. */
  ~Integer() {}

  /** Returns a copy of d_value to enable public access of GMP data. */
  const mpz_class& getValue() const { return d_value; }

  /** Overload copy assignment operator. */
  Integer& operator=(const Integer& x);

  /** Overload equality comparison operator. */
  bool operator==(const Integer& y) const;
  /** Overload greater than comparison operator. */
  bool operator>(const Integer& y) const;
  /** Overload greater than or equal comparison operator. */
  bool operator>=(const Integer& y) const;

  /** Overload negation operator. */
  Integer operator-() const;
  /** Overload addition operator. */
  Integer operator+(const Integer& y) const;
  /** Overload multiplication operator. */
  Integer operator*(const Integer& y) const;

  /** Return the bit-wise or of this and the given Integer. */
  Integer bitwiseOr(const Integer& y) const;
  /** Return the bit-wise and of this and the given Integer. */
  Integer bitwiseAnd(const Integer& y) const;
  /** Return the bit-wise exclusive or of this and the given Integer. */
  Integer bitwiseXor(const Integer& y) const;
  /** Return the bit-wise not of this Integer. */
  Integer bitwiseNot() const;

  /** Return this*(2^pow). */
  Integer multiplyByPow2(uint32_t pow) const;

  /**
   * Returns the integer with the binary representation of 'size' bits
   * extended with 'amount' 1's.
   */
  Integer oneExtend(uint32_t size, uint32_t amount) const;

  /** Return true if this Integer fits into an unsigned int. */
  bool fitsUnsignedInt() const;
  /** Return a 32 bit unsigned integer representation of this Integer. */
  uint32_t toUnsignedInt() const;

  /**
   * Extract a range of bits from index 'low' to (excluding) 'low + bitCount'.
   * Note: corresponds to the extract operator of theory BV.
   */
  Integer extractBitRange(uint32_t bitCount, uint32_t low) const;

  /** Returns the floor(this / y) */
  Integer floorDivideQuotient(const Integer& y) const;

  /** Returns r == this - floor(this/y)*y */
  Integer floorDivideRemainder(const Integer& y) const;

  /**
   * Computes a quotient and remainder according to Boute's Euclidean
   * definition. euclidianDivideQuotient, euclidianDivideRemainder.
   *
   * Boute, Raymond T. (April 1992).
   * The Euclidean definition of the functions div and mod.
   * ACM Transactions on Programming Languages and Systems (TOPLAS)
   * ACM Press. 14 (2): 127 - 144. doi:10.1145/128861.128862.
   */
  static void euclidianQR(Integer& q,
                          Integer& r,
                          const Integer& x,
                          const Integer& y);

  /**
   * Returns the quotient according to Boute's Euclidean definition.
   * See the documentation for euclidianQR.
   */
  Integer euclidianDivideQuotient(const Integer& y) const;

  /**
   * Returns the remainder according to Boute's Euclidean definition.
   * See the documentation for euclidianQR.
   */
  Integer euclidianDivideRemainder(const Integer& y) const;

  /** Returns y mod 2^exp. */
  Integer modByPow2(uint32_t exp) const;

  /** Return 1 if this is > 0, 0 if it is 0, and -1 if it is < 0. */
  int sgn() const;

  /** Raise this Integer to the power 'exp'. */
  Integer pow(uint32_t exp) const;

  /** Return a string representation of this Integer. */
  std::string toString(int base = 10) const;

  /**
   * Computes the hash of the node from the first word of the
   * numerator, the denominator.
   */
  size_t hash() const;

  /** */
  static size_t gmpHash(const mpz_t toHash);

  /**
   * If x != 0, returns the smallest n s.t. 2^{n-1} <= abs(x) < 2^{n}.
   * If x == 0, returns 1.
   */
  size_t length() const;

 private:
  /**
   * Gets a reference to the gmp data that backs up the integer.
   * Only accessible to friend classes.
   */
  const mpz_class& get_mpz() const { return d_value; }

  /**
   * The value of the rational is stored in a C++ GMP integer class.
   * Using this instead of mpz_t allows for easier destruction.
   */
  mpz_class d_value;
}; /* class Integer */


struct IntegerHashFunction
{
  inline size_t operator()(const Integer& i) const { return i.hash(); }
};

}  // namespace cvc5::internal

#endif
