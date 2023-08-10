#ifndef LITERAL_H
#define LITERAL_H

#include <sstream>
#include <string>
#include "util/rational.h"
#include "util/integer.h"
#include "kind.h"
#include "expr.h"

namespace alfc {

struct Literal
{
  /* Describes which type of result is being stored */
  enum
  {
    BOOL,
    INTEGER,
    RATIONAL,
    BITVECTOR,
    STRING,
    INVALID
  } d_tag;

  /* Stores the actual result */
  union
  {
    bool d_bool;
    Integer d_int;
    Rational d_rat;
    //BitVector d_bv;
    //String d_str;
  };

  Literal(const Literal& other);
  Literal() : d_tag(INVALID) {}
  Literal(bool b) : d_tag(BOOL), d_bool(b) {}
  Literal(const Integer& i) : d_tag(INTEGER), d_int(i) {}
  Literal(const Rational& r) : d_tag(RATIONAL), d_rat(r) {}
  //Literal(const BitVector& bv) : d_tag(BITVECTOR), d_bv(bv) {}
  //Literal(const String& str) : d_tag(STRING), d_str(str) {}

  Literal& operator=(const Literal& other);

  ~Literal() {}

  Kind toKind() const;
  std::string toString() const;

  /** Evaluate literal op */
  static Literal evaluate(Kind k, const std::vector<Literal*>& args);
};

}  // namespace alfc

#endif
