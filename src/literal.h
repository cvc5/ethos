#ifndef LITERAL_H
#define LITERAL_H

#include <sstream>
#include <string>
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/integer.h"
#include "util/string.h"
#include "kind.h"
#include "expr.h"

namespace alfc {

class Literal : public ExprValue
{
public:
  /* Stores the actual result */
  union
  {
    bool d_bool;
    Integer d_int;
    Rational d_rat;
    BitVector d_bv;
    String d_str;
    std::string d_sym;
  };

  Literal(const Literal& other);
  Literal() {}
  Literal(bool b) : ExprValue(Kind::BOOLEAN, {}), d_bool(b) {}
  Literal(const Integer& i) : ExprValue(Kind::NUMERAL, {}), d_int(i) {}
  Literal(Kind k, const Rational& r) : ExprValue(k, {}), d_rat(r) {}
  Literal(Kind k, const BitVector& bv) : ExprValue(k, {}), d_bv(bv) {}
  Literal(const String& str) : ExprValue(Kind::STRING, {}), d_str(str) {}
  Literal(Kind k, const std::string& sym) : ExprValue(k, {}), d_sym(sym) {}

  Literal& operator=(const Literal& other);

  ~Literal() {}
  /** as literal */
  const Literal* asLiteral() const override { return this; }
  std::string toString() const;

  /** Evaluate literal op */
  static Literal evaluate(Kind k, const std::vector<const Literal*>& args);
};

}  // namespace alfc

#endif
