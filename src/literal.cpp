#include "literal.h"

#include "base/check.h"

namespace alfc {

Literal::Literal(const Literal& other)
{
  d_tag = other.d_tag;
  switch (d_tag)
  {
    case BOOL: d_bool = other.d_bool; break;
    case RATIONAL:
      new (&d_rat) Rational;
      d_rat = other.d_rat;
      break;
    case INTEGER:
      new (&d_int) Integer;
      d_int = other.d_int;
      break;
    case BITVECTOR:
      //new (&d_bv) BitVector;
      //d_bv = other.d_bv;
      break;
    case STRING:
      //new (&d_str) String;
      //d_str = other.d_str;
      break;
    case INVALID: break;
  }
}

Literal& Literal::operator=(const Literal& other)
{
  if (this != &other)
  {
    d_tag = other.d_tag;
    switch (d_tag)
    {
      case BOOL: d_bool = other.d_bool; break;
      case RATIONAL:
        new (&d_rat) Rational;
        d_rat = other.d_rat;
        break;
      case INTEGER:
        new (&d_int) Integer;
        d_int = other.d_int;
        break;
      case BITVECTOR:
        //new (&d_bv) BitVector;
        //d_bv = other.d_bv;
        break;
      case STRING:
        //new (&d_str) String;
        //d_str = other.d_str;
        break;
      case INVALID: break;
    }
  }
  return *this;
}

// TODO: operators should be function variables or kinds???

Literal Literal::evaluate(Kind k, const std::vector<Literal*>& args)
{
  switch (k)
  {
    case Kind::NUMERAL_ADD:
    {
      Integer i;
      for (Literal* l : args)
      {
        Assert (l->d_tag==INTEGER);
        i = i + l->d_int;
      }
    }
      break;
    default:break;
  }
  return Literal();
}

}  // namespace alfc

