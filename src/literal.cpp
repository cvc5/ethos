#include "literal.h"

#include "base/check.h"
#include <iostream>

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

Kind Literal::toKind() const
{
  switch (d_tag)
  {
    case BOOL: return Kind::BOOLEAN;
    case RATIONAL: return Kind::DECIMAL;
    case INTEGER: return Kind::NUMERAL;
    case BITVECTOR: return Kind::BINARY;
    case STRING: return Kind::STRING;
    case INVALID: break;
    default:break;
  }
  ALFC_FATAL() << "Cannot convert literal to kind " << d_tag;
  return Kind::NONE;
}
std::string Literal::toString() const
{
  switch (d_tag)
  {
    case BOOL: return d_bool ? "true" : "false";
    case RATIONAL: return d_rat.toString();
    case INTEGER: return d_int.toString();
    case BITVECTOR:
    case STRING:
    case INVALID: break;
    default:break;
  }
  ALFC_FATAL() << "Cannot convert literal to string " << d_tag;
  return "?";
}

Expr Literal::getType(Kind k, std::vector<Expr>& childTypes)
{
  switch (k)
  {
    case Kind::NUMERAL_ADD:
      return childTypes[0];
      break;
    default:break;
  }
  return nullptr;
}

Literal Literal::evaluate(Kind k, const std::vector<Literal*>& args)
{
  switch (k)
  {
    case Kind::NUMERAL_ADD:
    {
      switch (args[0]->d_tag)
      {
        case INTEGER:
        {
          Integer i;
          for (Literal* l : args)
          {
            if (l->d_tag!=INTEGER)
            {
              return Literal();
            }
            i = i + l->d_int;
          }
          return Literal(Integer(i));
        }
        break;
        case RATIONAL:
        {
          Rational r;
          for (Literal* l : args)
          {
            if (l->d_tag!=RATIONAL)
            {
              return Literal();
            }
            r = r + l->d_rat;
          }
          return Literal(Rational(r));
        }
        break;
        default: break;
      }
    }
      break;
    default:break;
  }
  return Literal();
}

}  // namespace alfc

