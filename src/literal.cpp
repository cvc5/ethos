#include "literal.h"

#include "base/check.h"
#include <iostream>

namespace alfc {

Literal::Literal(const Literal& other)
{
  d_kind = other.d_kind;
  switch (d_kind)
  {
    case Kind::BOOLEAN: d_bool = other.d_bool; break;
    case Kind::DECIMAL:
      new (&d_rat) Rational;
      d_rat = other.d_rat;
      break;
    case Kind::NUMERAL:
      new (&d_int) Integer;
      d_int = other.d_int;
      break;
    case Kind::BINARY:
      new (&d_bv) BitVector;
      d_bv = other.d_bv;
      break;
    case Kind::STRING:
      new (&d_str) String;
      d_str = other.d_str;
      break;
    case Kind::NONE:
      break;
    default:
      Assert (isSymbol(d_kind));
      new (&d_sym) std::string;
      d_sym = other.d_sym;
      break;
  }
}

Literal& Literal::operator=(const Literal& other)
{
  if (this != &other)
  {
    d_kind = other.d_kind;
    switch (d_kind)
    {
      case Kind::BOOLEAN: d_bool = other.d_bool; break;
      case Kind::DECIMAL:
        new (&d_rat) Rational;
        d_rat = other.d_rat;
        break;
      case Kind::NUMERAL:
        new (&d_int) Integer;
        d_int = other.d_int;
        break;
      case Kind::BINARY:
        new (&d_bv) BitVector;
        d_bv = other.d_bv;
        break;
      case Kind::STRING:
        new (&d_str) String;
        d_str = other.d_str;
        break;
      case Kind::NONE:
        break;
      default:
        Assert (isSymbol(d_kind));
        new (&d_sym) std::string;
        d_sym = other.d_sym;
        break;
    }
  }
  return *this;
}

std::string Literal::toString() const
{
  switch (d_kind)
  {
    case Kind::BOOLEAN: return d_bool ? "true" : "false";
    case Kind::DECIMAL: return d_rat.toString();
    case Kind::NUMERAL: return d_int.toString();
    case Kind::BINARY: return d_bv.toString();
    case Kind::STRING: return d_str.toString();
    case Kind::NONE: break;
    default:
      Assert(isSymbol(d_kind));
      return d_sym;
      break;
  }
  ALFC_FATAL() << "Cannot convert literal to string " << d_kind;
  return "?";
}

Literal Literal::evaluate(Kind k, const std::vector<const Literal*>& args)
{
  Assert (k!=Kind::EVAL_IS_EQ && k!=Kind::EVAL_IF_THEN_ELSE && k!=Kind::EVAL_REQUIRES);
  switch (k)
  {
    // boolean
    case Kind::EVAL_NOT:
      switch (args[0]->d_kind)
      {
        case Kind::BOOLEAN:return Literal(!args[0]->d_bool);
        case Kind::BINARY:return Literal(~args[0]->d_bv);
        default: break;
      }
      break;
    case Kind::EVAL_AND:
      if (args[0]->d_kind==args[1]->d_kind)
      {
        switch (args[0]->d_kind)
        {
          case Kind::BOOLEAN:return Literal(args[0]->d_bool && args[1]->d_bool);
          case Kind::BINARY:return Literal(args[0]->d_bv & args[1]->d_bv);
          default: break;
        }
      }
      break;
    case Kind::EVAL_OR:
      if (args[0]->d_kind==args[1]->d_kind)
      {
        switch (args[0]->d_kind)
        {
          case Kind::BOOLEAN:return Literal(args[0]->d_bool || args[1]->d_bool);
          case Kind::BINARY:return Literal(args[0]->d_bv | args[1]->d_bv);
          default: break;
        }
      }
      break;
    case Kind::EVAL_ADD:
      // we allow mixed arithmetic here
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:
        switch (args[1]->d_kind)
        {
          case Kind::DECIMAL:return Literal(Rational(args[0]->d_int) + args[1]->d_rat);
          case Kind::NUMERAL:return Literal(args[0]->d_int + args[1]->d_int);
          default:break;
        }
        break;
        case Kind::DECIMAL:
        switch (args[1]->d_kind)
        {
          case Kind::NUMERAL:return Literal(args[0]->d_rat + Rational(args[1]->d_int));
          case Kind::DECIMAL:return Literal(args[0]->d_rat + args[1]->d_rat);
          default:break;
        }
        break;
        case Kind::BINARY:
          if (args[1]->d_kind==Kind::BINARY)
          {
            return Literal(args[0]->d_bv + args[1]->d_bv);
          }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_NEG:
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:return Literal(-args[0]->d_int);
        case Kind::DECIMAL:return Literal(-args[0]->d_rat);
        case Kind::BINARY:return Literal(-args[0]->d_bv);
        default: break;
      }
      break;
    case Kind::EVAL_MUL:
      // we allow mixed arithmetic here
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:
        switch (args[1]->d_kind)
        {
          case Kind::DECIMAL:return Literal(Rational(args[0]->d_int) * args[1]->d_rat);
          case Kind::NUMERAL:return Literal(args[0]->d_int * args[1]->d_int);
          default:break;
        }
        break;
        case Kind::DECIMAL:
        switch (args[1]->d_kind)
        {
          case Kind::NUMERAL:return Literal(args[0]->d_rat * Rational(args[1]->d_int));
          case Kind::DECIMAL:return Literal(args[0]->d_rat * args[1]->d_rat);
          default:break;
        }
        break;
        case Kind::BINARY:
          if (args[1]->d_kind==Kind::BINARY)
          {
            return Literal(args[0]->d_bv * args[1]->d_bv);
          }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_INT_DIV:
      if (args[0]->d_kind==args[1]->d_kind)
      {
        switch (args[0]->d_kind)
        {
          case Kind::NUMERAL:
          {
            const Integer& d = args[1]->d_int;
            if (d.sgn()!=0)
            {
              return Literal(Integer(args[0]->d_int.euclidianDivideQuotient(d)));
            }
          }
            break;
          case Kind::BINARY:
            return Literal(BitVector(args[0]->d_bv.unsignedDivTotal(args[1]->d_bv)));
            break;
          default: break;
        }
      }
      break;
    case Kind::EVAL_RAT_DIV:
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:
          if (args[1]->d_kind==Kind::NUMERAL)
          {
            const Integer& d = args[1]->d_int;
            if (d.sgn()!=0)
            {
              return Literal(Rational(args[0]->d_int, d));
            }
          }
          break;
        case Kind::DECIMAL:
          if (args[1]->d_kind==Kind::DECIMAL)
          {
            const Rational& d = args[1]->d_rat;
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
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:return Literal(args[0]->d_int.sgn()==-1);
        case Kind::DECIMAL:return Literal(args[0]->d_rat.sgn()==-1);
        default: break;
      }
      break;
    case Kind::EVAL_IS_ZERO:
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:return Literal(args[0]->d_int.sgn()==0);
        case Kind::DECIMAL:return Literal(args[0]->d_rat.sgn()==0);
        default: break;
      }
      break;
    // strings
    case Kind::EVAL_LENGTH:
      switch (args[0]->d_kind)
      {
        case Kind::BINARY:return Literal(Integer(args[0]->d_bv.getSize()));
        case Kind::STRING:return Literal(Integer(args[0]->d_str.size()));
        default: break;
      }
      break;
    case Kind::EVAL_CONCAT:
      if (args[0]->d_kind==args[1]->d_kind)
      {
        switch (args[0]->d_kind)
        {
          case Kind::BINARY:return Literal(args[0]->d_bv.concat(args[1]->d_bv));
          case Kind::STRING:return Literal(args[0]->d_str.concat(args[1]->d_str));
          default: break;
        }
      }
      break;
    case Kind::EVAL_EXTRACT:
      if (args[0]->d_kind==Kind::NUMERAL && args[0]->d_int.fitsUnsignedInt() &&
          args[1]->d_kind==Kind::NUMERAL && args[1]->d_int.fitsUnsignedInt())
      {
        uint32_t v1 = args[0]->d_int.toUnsignedInt();
        uint32_t v2 = args[1]->d_int.toUnsignedInt();
        switch (args[2]->d_kind)
        {
          // extract is high to low
          case Kind::BINARY:
            if (v1<=v2)
            {
              return Literal(args[2]->d_bv.extract(v2, v1));
            }
            break;
          case Kind::STRING:
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
      switch (args[0]->d_kind)
      {
        case Kind::DECIMAL:return Literal(args[0]->d_rat.floor());
        case Kind::NUMERAL: return *args[0];
        case Kind::BINARY:return Literal(args[0]->d_bv.getValue());
        case Kind::STRING:
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
      switch (args[0]->d_kind)
      {
        case Kind::DECIMAL: return *args[0];
        case Kind::NUMERAL:return Literal(Rational(args[0]->d_int));
        default: break;
      }
      break;
    case Kind::EVAL_TO_BV:
      if (args[0]->d_kind==Kind::NUMERAL && args[0]->d_int.fitsUnsignedInt())
      {
        uint32_t size = args[0]->d_int.toUnsignedInt();
        switch (args[0]->d_kind)
        {
          case Kind::NUMERAL:return Literal(BitVector(size, args[0]->d_int));
          case Kind::BINARY:return Literal(BitVector(size, args[0]->d_bv.getValue()));
          default: break;
        }
      }
      break;
    case Kind::EVAL_TO_STRING:
      switch (args[0]->d_kind)
      {
        case Kind::DECIMAL:
        case Kind::NUMERAL:
        case Kind::BINARY:return Literal(String(args[0]->toString()));
        case Kind::STRING: return *args[0];break;
        default: break;
      }
      break;
    default:break;
  }
  return Literal();
}

}  // namespace alfc

