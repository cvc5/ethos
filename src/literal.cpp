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
      new (&d_bv) BitVector;
      d_bv = other.d_bv;
      break;
    case STRING:
      new (&d_str) String;
      d_str = other.d_str;
      break;
    case SYMBOL:
      new (&d_sym) std::string;
      d_sym = other.d_sym;
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
        new (&d_bv) BitVector;
        d_bv = other.d_bv;
        break;
      case STRING:
        new (&d_str) String;
        d_str = other.d_str;
        break;
      case SYMBOL:
        new (&d_sym) std::string;
        d_sym = other.d_sym;
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
    case BITVECTOR: return d_bv.toString();
    case STRING: return d_str.toString();
    case SYMBOL: return d_sym;
    case INVALID: break;
    default:break;
  }
  ALFC_FATAL() << "Cannot convert literal to string " << d_tag;
  return "?";
}

Literal Literal::evaluate(Kind k, const std::vector<Literal*>& args)
{
  Assert (k!=Kind::EVAL_IS_EQ && k!=Kind::EVAL_IF_THEN_ELSE && k!=Kind::EVAL_REQUIRES);
  switch (k)
  {
    // boolean
    case Kind::EVAL_NOT:
      switch (args[0]->d_tag)
      {
        case BOOL:return Literal(!args[0]->d_bool);
        case BITVECTOR:return Literal(~args[0]->d_bv);
        default: break;
      }
      break;
    case Kind::EVAL_AND:
      if (args[0]->d_tag==args[1]->d_tag)
      {
        switch (args[0]->d_tag)
        {
          case BOOL:return Literal(args[0]->d_bool && args[1]->d_bool);
          case BITVECTOR:return Literal(args[0]->d_bv & args[1]->d_bv);
          default: break;
        }
      }
      break;
    case Kind::EVAL_OR:
      if (args[0]->d_tag==args[1]->d_tag)
      {
        switch (args[0]->d_tag)
        {
          case BOOL:return Literal(args[0]->d_bool || args[1]->d_bool);
          case BITVECTOR:return Literal(args[0]->d_bv | args[1]->d_bv);
          default: break;
        }
      }
      break;
    case Kind::EVAL_ADD:
      // TODO: allow mixed??
      if (args[0]->d_tag==args[1]->d_tag)
      {
        switch (args[0]->d_tag)
        {
          case INTEGER:return Literal(args[0]->d_int + args[1]->d_int);
          case RATIONAL:return Literal(args[0]->d_rat + args[1]->d_rat);
          case BITVECTOR:return Literal(args[0]->d_bv + args[1]->d_bv);
          default: break;
        }
      }
      break;
    case Kind::EVAL_NEG:
      switch (args[0]->d_tag)
      {
        case INTEGER:return Literal(-args[0]->d_int);
        case RATIONAL:return Literal(-args[0]->d_rat);
        case BITVECTOR:return Literal(-args[0]->d_bv);
        default: break;
      }
      break;
    case Kind::EVAL_MUL:
      // TODO: allow mixed??
      if (args[0]->d_tag==args[1]->d_tag)
      {
        switch (args[0]->d_tag)
        {
          case INTEGER:return Literal(args[0]->d_int * args[1]->d_int);
          case RATIONAL:return Literal(args[0]->d_rat * args[1]->d_rat);
          case BITVECTOR:return Literal(args[0]->d_bv * args[1]->d_bv);
          default: break;
        }
      }
      break;
    case Kind::EVAL_INT_DIV:
      if (args[0]->d_tag==args[1]->d_tag)
      {
        switch (args[0]->d_tag)
        {
          case INTEGER:
          {
            Integer& d = args[1]->d_int;
            if (d.sgn()!=0)
            {
              return Literal(Integer(args[0]->d_int.euclidianDivideQuotient(d)));
            }
          }
            break;
          case BITVECTOR:
            // TODO
            break;
          default: break;
        }
      }
      break;
    case Kind::EVAL_RAT_DIV:
      switch (args[0]->d_tag)
      {
        case INTEGER:
          if (args[1]->d_tag==INTEGER)
          {
            Integer& d = args[1]->d_int;
            if (d.sgn()!=0)
            {
              return Literal(Rational(args[0]->d_int, d));
            }
          }
          break;
        case RATIONAL:
          if (args[1]->d_tag==RATIONAL)
          {
            Rational& d = args[1]->d_rat;
            if (d.sgn()!=0)
            {
              return Literal(Rational(args[0]->d_rat / d));
            }
          }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_IS_NEG:
      switch (args[0]->d_tag)
      {
        case INTEGER:return Literal(args[0]->d_int.sgn()==-1);
        case RATIONAL:return Literal(args[0]->d_rat.sgn()==-1);
        default: break;
      }
      break;
    case Kind::EVAL_IS_ZERO:
      switch (args[0]->d_tag)
      {
        case INTEGER:return Literal(args[0]->d_int.sgn()==0);
        case RATIONAL:return Literal(args[0]->d_rat.sgn()==0);
        default: break;
      }
      break;
    // strings
    case Kind::EVAL_LENGTH:
      switch (args[0]->d_tag)
      {
        case BITVECTOR:return Literal(Integer(args[0]->d_bv.getSize()));
        case STRING:return Literal(Integer(args[0]->d_str.size()));
        default: break;
      }
      break;
    case Kind::EVAL_CONCAT:
      if (args[0]->d_tag==args[1]->d_tag)
      {
        switch (args[0]->d_tag)
        {
          case BITVECTOR:return Literal(args[0]->d_bv.concat(args[1]->d_bv));
          case STRING:return Literal(args[0]->d_str.concat(args[1]->d_str));
          default: break;
        }
      }
      break;
    case Kind::EVAL_EXTRACT:
      if (args[0]->d_tag==INTEGER && args[0]->d_int.fitsUnsignedInt() &&
          args[1]->d_tag==INTEGER && args[1]->d_int.fitsUnsignedInt())
      {
        uint32_t v1 = args[0]->d_int.toUnsignedInt();
        uint32_t v2 = args[1]->d_int.toUnsignedInt();
        switch (args[2]->d_tag)
        {
          // extract is high to low
          case BITVECTOR:
            if (v1<=v2)
            {
              return Literal(args[2]->d_bv.extract(v2, v1));
            }
            break;
          case STRING:
          {
            size_t ssize = v2>=v1 ? (v2-v1) : 0;
            return Literal(String(args[2]->d_str.substr(v1, ssize)));
          }
            break;
          default: break;
        }
      }
      break;
    // conversions
    case Kind::EVAL_TO_INT:
      switch (args[0]->d_tag)
      {
        case RATIONAL:return Literal(args[0]->d_rat.floor());
        case INTEGER: return *args[0];
        case BITVECTOR:return Literal(args[0]->d_bv.getValue());
        case STRING:
        {
          if (args[0]->d_str.isNumber())
          {
            return Literal(Integer(args[0]->d_str.toString()));
          }
        }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_TO_RAT:
      switch (args[0]->d_tag)
      {
        case RATIONAL: return *args[0];
        case INTEGER:return Literal(Rational(args[0]->d_int));
        default: break;
      }
      break;
    case Kind::EVAL_TO_BV:
      if (args[0]->d_tag==INTEGER && args[0]->d_int.fitsUnsignedInt())
      {
        uint32_t size = args[0]->d_int.toUnsignedInt();
        switch (args[0]->d_tag)
        {
          case INTEGER:return Literal(BitVector(size, args[0]->d_int));
          case BITVECTOR:return Literal(BitVector(size, args[0]->d_bv.getValue()));
          default: break;
        }
      }
      break;
    case Kind::EVAL_TO_STRING:
      switch (args[0]->d_tag)
      {
        case RATIONAL:
        case INTEGER:
        case BITVECTOR:return Literal(String(args[0]->toString()));
        case STRING: return *args[0];break;
        default: break;
      }
      break;
    default:break;
  }
  return Literal();
}

}  // namespace alfc

