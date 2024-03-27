/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include <cmath>
#include <sstream>
#include <string>
#include <iostream>
#include <gmpxx.h>

#include "rational.h"

namespace alfc {

std::ostream& operator<<(std::ostream& os, const Rational& q){
  return os << q.toString();
}

/* Computes a rational given a decimal string. The rational
 * version of <code>xxx.yyy</code> is <code>xxxyyy/(10^3)</code>.
 */
Rational Rational::fromDecimal(const std::string& dec) {
  using std::string;
  // Find the decimal point, if there is one
  string::size_type i( dec.find(".") );
  if( i != string::npos ) {
    /* Erase the decimal point, so we have just the numerator. */
    Integer numerator( string(dec).erase(i,1) );

    /* Compute the denominator: 10 raise to the number of decimal places */
    int decPlaces = dec.size() - (i + 1);
    Integer denominator( Integer(10).pow(decPlaces) );

    return Rational( numerator, denominator );
  } else {
    /* No decimal point, assume it's just an integer. */
    return Rational( dec );
  }
}

bool Rational::isIntegral() const { return mpz_cmp_ui(d_value.get_den_mpz_t(), 1) == 0; }

std::string Rational::toString(int base) const { return d_value.get_str(base); }
std::string Rational::toStringDecimal() const
{
  // NOTE: we simply print as a rational for now, due to limitations in
  // how decimals should be printed.
  return toString();
  /*
  // truncate to 256 digits
  // NOTE: this method is not used since it has limitations. We always print
  // decimals as rationals.
  mpf_class floatValue(d_value);
  char buf[500];
  gmp_sprintf(buf, "%.256Fg", floatValue);
  std::stringstream ss;
  ss << buf;
  return ss.str();
  */
}

}  // namespace alfc
