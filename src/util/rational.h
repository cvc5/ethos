#ifndef RATIONAL_H
#define RATIONAL_H

#include <gmp.h>

#include <optional>
#include <string>

#include "integer.h"

namespace alfc {

/**
 * A multi-precision rational constant.
 * This stores the rational as a pair of multi-precision integers,
 * one for the numerator and one for the denominator.
 * The number is always stored so that the gcd of the numerator and denominator
 * is 1.  (This is referred to as referred to as canonical form in GMP's
 * literature.) A consequence is that that the numerator and denominator may be
 * different than the values used to construct the Rational.
 */
class Rational
{
 public:
  /**
   * Constructs a Rational from a mpq_class object.
   * Does a deep copy.
   * Assumes that the value is in canonical form, and thus does not
   * have to call canonicalize() on the value.
   */
  Rational(const mpq_class& val) : d_value(val) {}

  /**
   * Creates a rational from a decimal string (e.g., <code>"1.5"</code>).
   *
   * @param dec a string encoding a decimal number in the format
   * <code>[0-9]*\.[0-9]*</code>
   */
  static Rational fromDecimal(const std::string& dec);

  /** Constructs a rational with the value 0/1. */
  Rational() : d_value(0) { d_value.canonicalize(); }

  Rational(const std::string& s, unsigned base = 10) : d_value(s, base)
  {
    d_value.canonicalize();
  }

  /**
   * Creates a Rational from another Rational, q, by performing a deep copy.
   */
  Rational(const Rational& q) : d_value(q.d_value) { d_value.canonicalize(); }

  Rational(const Integer& n, const Integer& d)
      : d_value(n.get_mpz(), d.get_mpz())
  {
    d_value.canonicalize();
  }
  Rational(const Integer& n) : d_value(n.get_mpz()) { d_value.canonicalize(); }
  ~Rational() {}

  int sgn() const { return mpq_sgn(d_value.get_mpq_t()); }

  Integer floor() const
  {
    mpz_class q;
    mpz_fdiv_q(q.get_mpz_t(), d_value.get_num_mpz_t(), d_value.get_den_mpz_t());
    return Integer(q);
  }

  Integer ceiling() const
  {
    mpz_class q;
    mpz_cdiv_q(q.get_mpz_t(), d_value.get_num_mpz_t(), d_value.get_den_mpz_t());
    return Integer(q);
  }

  Rational& operator=(const Rational& x)
  {
    if (this == &x) return *this;
    d_value = x.d_value;
    return *this;
  }

  Rational operator-() const { return Rational(-(d_value)); }

  bool operator==(const Rational& y) const { return d_value == y.d_value; }

  Rational operator+(const Rational& y) const
  {
    return Rational(d_value + y.d_value);
  }

  Rational operator*(const Rational& y) const
  {
    return Rational(d_value * y.d_value);
  }
  Rational operator/(const Rational& y) const
  {
    return Rational(d_value / y.d_value);
  }

  bool isIntegral() const;

  /** Returns a string representing the rational in the given base. */
  std::string toString(int base = 10) const { return d_value.get_str(base); }

 private:
  /**
   * Stores the value of the rational is stored in a C++ GMP rational class.
   * Using this instead of mpq_t allows for easier destruction.
   */
  mpq_class d_value;

}; /* class Rational */

}  // namespace alfc

#endif
