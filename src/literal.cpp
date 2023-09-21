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
    case Kind::RATIONAL:
      new (&d_rat) Rational;
      d_rat = other.d_rat;
      break;
    case Kind::NUMERAL:
      new (&d_int) Integer;
      d_int = other.d_int;
      break;
    case Kind::HEXADECIMAL:
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
      case Kind::RATIONAL:
        new (&d_rat) Rational;
        d_rat = other.d_rat;
        break;
      case Kind::NUMERAL:
        new (&d_int) Integer;
        d_int = other.d_int;
        break;
      case Kind::HEXADECIMAL:
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
    case Kind::DECIMAL:
    case Kind::RATIONAL: return d_rat.toString();
    case Kind::NUMERAL: return d_int.toString();
    case Kind::HEXADECIMAL:
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

Kind allSameKind(const std::vector<const Literal*>& args)
{
  Kind k = args[0]->getKind();
  for (size_t i=1, nargs=args.size(); i<nargs; i++)
  {
    if (args[i]->getKind()!=k)
    {
      return Kind::NONE;
    }
  }
  return k;
}

Literal Literal::evaluate(Kind k, const std::vector<const Literal*>& args)
{
  Assert (k!=Kind::EVAL_IS_EQ && k!=Kind::EVAL_IF_THEN_ELSE && k!=Kind::EVAL_REQUIRES);
  /*
  Kind ka = Kind::NONE;
  if (k!=Kind::EVAL_EXTRACT && k!=Kind::EVAL_TO_BV)
  {
    ka = allSameKind(args);
    if (ka==Kind::NONE)
    {
      return Literal();
    }
  }
  */
  switch (k)
  {
    // boolean
    case Kind::EVAL_NOT:
      switch (args[0]->d_kind)
      {
        case Kind::BOOLEAN:return Literal(!args[0]->d_bool);
        case Kind::HEXADECIMAL:
        case Kind::BINARY:return Literal(args[0]->d_kind, ~args[0]->d_bv);
        default: break;
      }
      break;
    case Kind::EVAL_AND:
    case Kind::EVAL_OR:
    case Kind::EVAL_XOR:
    {
      Kind ka = allSameKind(args);
      if (ka==Kind::NONE)
      {
        return Literal();
      }
      switch (ka)
      {
        case Kind::BOOLEAN:
        {
          bool res = args[0]->d_bool;
          for (size_t i=1, nargs = args.size(); i<nargs; i++)
          {
            switch (k)
            {
            case Kind::EVAL_AND: res = (res && args[i]->d_bool); break;
            case Kind::EVAL_OR: res = (res || args[i]->d_bool); break;
            case Kind::EVAL_XOR:res = (res != args[i]->d_bool); break;
            default:break;
            }
          }
          return Literal(res);
        }
          break;
        case Kind::BINARY:
        {
          BitVector res = args[0]->d_bv;
          for (size_t i=1, nargs = args.size(); i<nargs; i++)
          {
            switch (k)
            {
            case Kind::EVAL_AND: res = (res & args[i]->d_bv); break;
            case Kind::EVAL_OR: res = (res | args[i]->d_bv); break;
            case Kind::EVAL_XOR:res = (res ^ args[i]->d_bv); break;
            default:break;
            }
          }
          return Literal(ka, res);
        }
          break;
        default:
          break;
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
          case Kind::RATIONAL:return Literal(Kind::RATIONAL, Rational(args[0]->d_int) + args[1]->d_rat);
          case Kind::NUMERAL:return Literal(args[0]->d_int + args[1]->d_int);
          default:break;
        }
        break;
        case Kind::RATIONAL:
        switch (args[1]->d_kind)
        {
          case Kind::NUMERAL:return Literal(Kind::RATIONAL, args[0]->d_rat + Rational(args[1]->d_int));
          case Kind::RATIONAL:return Literal(Kind::RATIONAL, args[0]->d_rat + args[1]->d_rat);
          default:break;
        }
        break;
        case Kind::BINARY:
        {
          Kind ka = allSameKind(args);
          if (ka==Kind::NONE)
          {
            return Literal();
          }
          return Literal(ka, args[0]->d_bv + args[1]->d_bv);
        }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_NEG:
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:return Literal(-args[0]->d_int);
        case Kind::DECIMAL:
        case Kind::RATIONAL:return Literal(args[0]->d_kind, -args[0]->d_rat);
        case Kind::HEXADECIMAL:
        case Kind::BINARY:return Literal(args[0]->d_kind, -args[0]->d_bv);
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
          case Kind::RATIONAL:return Literal(Kind::RATIONAL, Rational(args[0]->d_int) * args[1]->d_rat);
          case Kind::NUMERAL:return Literal(args[0]->d_int * args[1]->d_int);
          default:break;
        }
        break;
        case Kind::RATIONAL:
        switch (args[1]->d_kind)
        {
          case Kind::NUMERAL:return Literal(Kind::RATIONAL, args[0]->d_rat * Rational(args[1]->d_int));
          case Kind::RATIONAL:return Literal(Kind::RATIONAL, args[0]->d_rat * args[1]->d_rat);
          default:break;
        }
        break;
        case Kind::HEXADECIMAL:
        case Kind::BINARY:
        {
          Kind ka = allSameKind(args);
          if (ka==Kind::NONE)
          {
            return Literal();
          }
          return Literal(ka, args[0]->d_bv * args[1]->d_bv);
        }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_INT_DIV:
    {
      Kind ka = allSameKind(args);
      if (ka==Kind::NONE)
      {
        return Literal();
      }
      switch (ka)
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
        case Kind::HEXADECIMAL:
        case Kind::BINARY:
          return Literal(ka, BitVector(args[0]->d_bv.unsignedDivTotal(args[1]->d_bv)));
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
              return Literal(Kind::RATIONAL, Rational(args[0]->d_int, d));
            }
          }
          break;
        case Kind::DECIMAL:
        case Kind::RATIONAL:
          if (args[1]->d_kind==Kind::RATIONAL)
          {
            const Rational& d = args[1]->d_rat;
            if (d.sgn()!=0)
            {
              return Literal(Kind::RATIONAL, Rational(args[0]->d_rat / d));
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
        case Kind::DECIMAL:
        case Kind::RATIONAL:return Literal(args[0]->d_rat.sgn()==-1);
        default: break;
      }
      break;
    case Kind::EVAL_IS_ZERO:
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:return Literal(args[0]->d_int.sgn()==0);
        case Kind::DECIMAL:
        case Kind::RATIONAL:return Literal(args[0]->d_rat.sgn()==0);
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
    {
      Kind ka = allSameKind(args);
      if (ka==Kind::NONE)
      {
        return Literal();
      }
      switch (ka)
      {
        case Kind::HEXADECIMAL:
        case Kind::BINARY:
        {
          BitVector res = args[0]->d_bv;
          for (size_t i=1, nargs=args.size(); i<nargs; i++)
          {
            res = res.concat(args[i]->d_bv);
          }
          return Literal(ka, res);
        }
        case Kind::STRING:
        {
          String res = args[0]->d_str;
          for (size_t i=1, nargs=args.size(); i<nargs; i++)
          {
            res = res.concat(args[i]->d_str);
          }
          return Literal(res);
        }
          break;
        default: break;
      }
    }
      break;
    case Kind::EVAL_EXTRACT:
      if (args[1]->d_kind==Kind::NUMERAL && args[2]->d_kind==Kind::NUMERAL)
      {
        const Integer& i1 = args[1]->d_int;
        const Integer& i2 = args[2]->d_int;
        Kind ka = args[0]->d_kind;
        switch (ka)
        {
          // extract is high to low
          case Kind::HEXADECIMAL:
          case Kind::BINARY:
          {
            Integer dsize(args[0]->d_bv.getSize());
            if (i1.sgn()<0 || i2.sgn()<0 || i1>dsize || dsize.sgn()==0)
            {
              return Literal(ka, BitVector(0));
            }
            Assert (i1.fitsUnsignedInt() && dsize.fitsUnsignedInt());
            uint32_t v1 = i1.toUnsignedInt();
            uint32_t vs = dsize.toUnsignedInt();
            uint32_t v2 = i2>dsize ? vs-1 : i2.toUnsignedInt();
            if (v1>v2)
            {
              return Literal(ka, BitVector(0));
            }
            return Literal(ka, args[0]->d_bv.extract(v2, v1));
          }
            break;
          case Kind::STRING:
          {
            Integer dsize(args[0]->d_str.size());
            if (i1.sgn()<0 || i2.sgn()<0 || i1>dsize || dsize.sgn()==0)
            {
              return Literal(String(""));
            }
            Assert (i1.fitsUnsignedInt() && dsize.fitsUnsignedInt());
            uint32_t v1 = i1.toUnsignedInt();
            uint32_t vs = dsize.toUnsignedInt();
            uint32_t v2 = (i1+i2)>=dsize ? vs-1 : i2.toUnsignedInt();
            size_t esize = v2>=v1 ? (v2+1-v1) : 0;
            return Literal(String(args[0]->d_str.substr(v1, esize)));
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
        case Kind::DECIMAL:
        case Kind::RATIONAL:return Literal(args[0]->d_rat.floor());
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
        case Kind::RATIONAL: return *args[0];
        case Kind::DECIMAL: return Literal(Kind::RATIONAL, args[0]->d_rat);
        case Kind::NUMERAL:return Literal(Kind::RATIONAL, Rational(args[0]->d_int));
        default: break;
      }
      break;
    case Kind::EVAL_TO_BV:
      if (args[0]->d_kind==Kind::NUMERAL && args[0]->d_int.fitsUnsignedInt())
      {
        uint32_t size = args[0]->d_int.toUnsignedInt();
        switch (args[1]->d_kind)
        {
          case Kind::NUMERAL:return Literal(Kind::BINARY, BitVector(size, args[1]->d_int));
          case Kind::HEXADECIMAL:
          case Kind::BINARY:return Literal(Kind::BINARY, BitVector(size, args[1]->d_bv.getValue()));
          default: break;
        }
      }
      break;
    case Kind::EVAL_TO_STRING:
      switch (args[0]->d_kind)
      {
        case Kind::NUMERAL:
        case Kind::DECIMAL:
        case Kind::RATIONAL:
        case Kind::HEXADECIMAL:
        case Kind::BINARY:return Literal(String(args[0]->toString()));
        case Kind::STRING: return *args[0];break;
        default: break;
      }
      break;
    case Kind::EVAL_FIND:
      if (args[0]->d_kind==args[1]->d_kind)
      {
        switch (args[0]->d_kind)
        {
          case Kind::STRING:
          {
            std::size_t i = args[0]->d_str.find(args[1]->d_str);
            if (i==std::string::npos)
            {
              return Literal(Integer("-1"));
            }
            return Literal(Integer(i));
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

