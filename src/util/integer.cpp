#include <cmath>
#include <limits>
#include <sstream>
#include <string>

#include "integer.h"

using namespace std;

namespace alfc {

Integer::Integer(const std::string& s, unsigned base)
  : d_value(s, base)
{}

Integer& Integer::operator=(const Integer& x)
{
  if (this == &x) return *this;
  d_value = x.d_value;
  return *this;
}

bool Integer::operator==(const Integer& y) const
{
  return d_value == y.d_value;
}

bool Integer::operator>(const Integer& y) const { return d_value > y.d_value; }

bool Integer::operator>=(const Integer& y) const { return d_value >= y.d_value; }

Integer Integer::operator-() const { return Integer(-(d_value)); }

Integer Integer::operator+(const Integer& y) const
{
  return Integer(d_value + y.d_value);
}

Integer Integer::operator*(const Integer& y) const
{
  return Integer(d_value * y.d_value);
}

Integer Integer::bitwiseOr(const Integer& y) const
{
  mpz_class result;
  mpz_ior(result.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer(result);
}

Integer Integer::bitwiseAnd(const Integer& y) const
{
  mpz_class result;
  mpz_and(result.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer(result);
}

Integer Integer::bitwiseXor(const Integer& y) const
{
  mpz_class result;
  mpz_xor(result.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer(result);
}

Integer Integer::bitwiseNot() const
{
  mpz_class result;
  mpz_com(result.get_mpz_t(), d_value.get_mpz_t());
  return Integer(result);
}

Integer Integer::multiplyByPow2(uint32_t pow) const
{
  mpz_class result;
  mpz_mul_2exp(result.get_mpz_t(), d_value.get_mpz_t(), pow);
  return Integer(result);
}

Integer Integer::oneExtend(uint32_t size, uint32_t amount) const
{
  // check that the size is accurate
  //Assert((*this) < Integer(1).multiplyByPow2(size));
  mpz_class res = d_value;

  for (unsigned i = size; i < size + amount; ++i)
  {
    mpz_setbit(res.get_mpz_t(), i);
  }

  return Integer(res);
}

bool Integer::fitsUnsignedInt() const { return d_value.fits_uint_p(); }

uint32_t Integer::toUnsignedInt() const
{
  return mpz_get_ui(d_value.get_mpz_t());
}

Integer Integer::extractBitRange(uint32_t bitCount, uint32_t low) const
{
  // bitCount = high-low+1
  uint32_t high = low + bitCount - 1;
  //- Function: void mpz_fdiv_r_2exp (mpz_t r, mpz_t n, mp_bitcnt_t b)
  mpz_class rem, div;
  mpz_fdiv_r_2exp(rem.get_mpz_t(), d_value.get_mpz_t(), high + 1);
  mpz_fdiv_q_2exp(div.get_mpz_t(), rem.get_mpz_t(), low);

  return Integer(div);
}

Integer Integer::floorDivideQuotient(const Integer& y) const
{
  mpz_class q;
  mpz_fdiv_q(q.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer(q);
}

Integer Integer::floorDivideRemainder(const Integer& y) const
{
  mpz_class r;
  mpz_fdiv_r(r.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer(r);
}

void Integer::floorQR(Integer& q,
                      Integer& r,
                      const Integer& x,
                      const Integer& y)
{
  mpz_fdiv_qr(q.d_value.get_mpz_t(),
              r.d_value.get_mpz_t(),
              x.d_value.get_mpz_t(),
              y.d_value.get_mpz_t());
}

Integer Integer::ceilingDivideQuotient(const Integer& y) const
{
  mpz_class q;
  mpz_cdiv_q(q.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer(q);
}

Integer Integer::ceilingDivideRemainder(const Integer& y) const
{
  mpz_class r;
  mpz_cdiv_r(r.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer(r);
}

void Integer::euclidianQR(Integer& q,
                          Integer& r,
                          const Integer& x,
                          const Integer& y)
{
  // compute the floor and then fix the value up if needed.
  floorQR(q, r, x, y);

  if (r.sgn()<0)
  {
    // if r < 0
    // abs(r) < abs(y)
    // - abs(y) < r < 0, then 0 < r + abs(y) < abs(y)
    // n = y * q + r
    // n = y * q - abs(y) + r + abs(y)
    if (r.sgn() >= 0)
    {
      // y = abs(y)
      // n = y * q - y + r + y
      // n = y * (q-1) + (r+y)
      q = q+(-Integer(1));
      r = r+y;
    }
    else
    {
      // y = -abs(y)
      // n = y * q + y + r - y
      // n = y * (q+1) + (r-y)
      q = q+Integer(1);
      r = r+(-y);
    }
  }
}

Integer Integer::euclidianDivideQuotient(const Integer& y) const
{
  Integer q, r;
  euclidianQR(q, r, *this, y);
  return q;
}

Integer Integer::euclidianDivideRemainder(const Integer& y) const
{
  Integer q, r;
  euclidianQR(q, r, *this, y);
  return r;
}

Integer Integer::exactQuotient(const Integer& y) const
{
  //Assert(y.divides(*this));
  mpz_class q;
  mpz_divexact(q.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer(q);
}

Integer Integer::modByPow2(uint32_t exp) const
{
  mpz_class res;
  mpz_fdiv_r_2exp(res.get_mpz_t(), d_value.get_mpz_t(), exp);
  return Integer(res);
}

Integer Integer::divByPow2(uint32_t exp) const
{
  mpz_class res;
  mpz_fdiv_q_2exp(res.get_mpz_t(), d_value.get_mpz_t(), exp);
  return Integer(res);
}

int Integer::sgn() const { return mpz_sgn(d_value.get_mpz_t()); }

Integer Integer::pow(uint32_t exp) const
{
  mpz_class result;
  mpz_pow_ui(result.get_mpz_t(), d_value.get_mpz_t(), exp);
  return Integer(result);
}

Integer Integer::modAdd(const Integer& y, const Integer& m) const
{
  mpz_class res;
  mpz_add(res.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  mpz_mod(res.get_mpz_t(), res.get_mpz_t(), m.d_value.get_mpz_t());
  return Integer(res);
}

Integer Integer::modMultiply(const Integer& y, const Integer& m) const
{
  mpz_class res;
  mpz_mul(res.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  mpz_mod(res.get_mpz_t(), res.get_mpz_t(), m.d_value.get_mpz_t());
  return Integer(res);
}

Integer Integer::modInverse(const Integer& m) const
{
  //Assert(m > 0) << "m must be greater than zero";
  mpz_class res;
  if (mpz_invert(res.get_mpz_t(), d_value.get_mpz_t(), m.d_value.get_mpz_t())
      == 0)
  {
    return Integer(-1);
  }
  return Integer(res);
}

bool Integer::divides(const Integer& y) const
{
  int res = mpz_divisible_p(y.d_value.get_mpz_t(), d_value.get_mpz_t());
  return res != 0;
}

std::string Integer::toString(int base) const { return d_value.get_str(base); }


size_t Integer::hash() const
{
  return gmpHash(d_value.get_mpz_t());
}

size_t Integer::gmpHash(const mpz_t toHash)
{
  size_t hash = 0;
  for (int i = 0, n = mpz_size(toHash); i < n; ++i){
    mp_limb_t limb = mpz_getlimbn(toHash, i);
    hash = hash * 2;
    hash = hash xor limb;
  }
  return hash;
}

bool Integer::testBit(unsigned n) const
{
  return mpz_tstbit(d_value.get_mpz_t(), n);
}

size_t Integer::length() const
{
  if (sgn() == 0)
  {
    return 1;
  }
  else
  {
    return mpz_sizeinbase(d_value.get_mpz_t(), 2);
  }
}

}  // namespace cvc5::internal
