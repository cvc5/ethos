/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "util/bitvector.h"

#include "base/check.h"

namespace alfc {

BitVector::BitVector(const std::string& num, uint32_t base)
{
  Assert(base == 2 || base == 10 || base == 16);
  Assert(num[0] != '-');
  d_value = Integer(num, base);
  Assert(d_value.sgn()>=0);
  // Compute the length, *without* any negative sign.
  switch (base)
  {
    case 10: d_size = d_value.length(); break;
    case 16: d_size = num.size() * 4; break;
    default: d_size = num.size();
  }
}

unsigned BitVector::getSize() const { return d_size; }

const Integer& BitVector::getValue() const { return d_value; }

Integer BitVector::toInteger() const { return d_value; }

std::string BitVector::toString(unsigned int base) const
{
  std::string str = d_value.toString(base);
  if (base == 2 && d_size > str.size())
  {
    std::string zeroes;
    for (unsigned int i = 0; i < d_size - str.size(); ++i)
    {
      zeroes.append("0");
    }
    return zeroes + str;
  }
  else
  {
    return str;
  }
}

size_t BitVector::hash() const
{
  return std::hash<size_t>()(d_value.hash()) ^ std::hash<size_t>()(d_size);
}

/* -----------------------------------------------------------------------
 * Operators
 * ----------------------------------------------------------------------- */

/* String Operations ----------------------------------------------------- */

BitVector BitVector::concat(const BitVector& other) const
{
  return BitVector(d_size + other.d_size,
                   (d_value.multiplyByPow2(other.d_size)) + other.d_value);
}

BitVector BitVector::extract(unsigned high, unsigned low) const
{
  Assert(high < d_size);
  Assert(low <= high);
  return BitVector(high - low + 1,
                   d_value.extractBitRange(high - low + 1, low));
}

/* (Dis)Equality --------------------------------------------------------- */

bool operator==(const BitVector& a, const BitVector& b)
{
  if (a.getSize() != b.getSize()) return false;
  return a.getValue() == b.getValue();
}

/* Bit-wise operations --------------------------------------------------- */

BitVector operator^(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  return BitVector(a.getSize(), a.getValue().bitwiseXor(b.getValue()));
}

BitVector operator|(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  return BitVector(a.getSize(), a.getValue().bitwiseOr(b.getValue()));
}

BitVector operator&(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  return BitVector(a.getSize(), a.getValue().bitwiseAnd(b.getValue()));
}

BitVector operator~(const BitVector& a)
{
  return BitVector(a.getSize(), a.getValue().bitwiseNot());
}

/* Arithmetic operations ------------------------------------------------- */

BitVector operator+(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  Integer sum = a.getValue() + b.getValue();
  return BitVector(a.getSize(), sum);
}

BitVector operator-(const BitVector& a)
{
  BitVector one(a.getSize(), Integer(1));
  return ~a + one;
}

BitVector operator*(const BitVector& a, const BitVector& b)
{
  Assert(a.getSize() == b.getSize());
  Integer prod = a.getValue() * b.getValue();
  return BitVector(a.getSize(), prod);
}

BitVector BitVector::unsignedDivTotal(const BitVector& y) const
{
  Assert(d_size == y.d_size);
  /* d_value / 0 = -1 = 2^d_size - 1 */
  if (y.d_value.sgn()==0)
  {
    return BitVector(d_size, Integer(1).oneExtend(1, d_size - 1));
  }
  Assert(d_value.sgn() >= 0);
  Assert(y.d_value.sgn() > 0);
  return BitVector(d_size, d_value.floorDivideQuotient(y.d_value));
}

BitVector BitVector::unsignedRemTotal(const BitVector& y) const
{
  Assert(d_size == y.d_size);
  if (y.d_value.sgn()==0)
  {
    return BitVector(d_size, d_value);
  }
  Assert(d_value.sgn() >= 0);
  Assert(y.d_value.sgn() > 0);
  return BitVector(d_size, d_value.floorDivideRemainder(y.d_value));
}

}  // namespace cvc5::internal
