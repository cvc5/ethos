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

Literal Literal::evaluate(Kind k, const std::vector<Literal*>& args)
{
  switch (k)
  {
    case Kind::EVAL_IS_EQ:
      // note if not properly typed, it does not evaluate
      if (args[0]->d_tag==args[1]->d_tag)
      {
        switch(args[0]->d_tag)
        {
        case BOOL: return Literal(args[0]->d_bool==args[1]->d_bool);break;
        case RATIONAL: return Literal(args[0]->d_rat==args[1]->d_rat);break;
        case INTEGER: return Literal(args[0]->d_int==args[1]->d_int);break;
        case BITVECTOR:
        case STRING:
        default: break;
        }
      }
      break;
    case Kind::EVAL_IF_THEN_ELSE:
      if (args[0]->d_tag==BOOL)
      {
        return Literal(args[0]->d_bool ? *args[1] : *args[2]);
      }
      break;
    // boolean
    case Kind::EVAL_NOT:
      if (args[0]->d_tag==BOOL)
      {
        return Literal(!args[0]->d_bool);
      }
    case Kind::EVAL_AND:
      switch (args[0]->d_tag)
      {
        case BOOL:
          if (args[1]->d_tag==BOOL)
          {
            return Literal(args[0]->d_bool && args[1]->d_bool);
          }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_OR:
      switch (args[0]->d_tag)
      {
        case BOOL:
          if (args[1]->d_tag==BOOL)
          {
            return Literal(args[0]->d_bool || args[1]->d_bool);
          }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_ADD:
      // TODO: allow mixed??
      switch (args[0]->d_tag)
      {
        case INTEGER:
          if (args[1]->d_tag==INTEGER)
          {
            return Literal(Integer(args[0]->d_int + args[1]->d_int));
          }
          break;
        case RATIONAL:
          if (args[1]->d_tag==RATIONAL)
          {
            return Literal(Rational(args[0]->d_rat + args[1]->d_rat));
          }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_NEG:
      switch (args[0]->d_tag)
      {
        case INTEGER:return Literal(Integer(-args[0]->d_int));
        case RATIONAL:return Literal(Rational(-args[0]->d_rat));
        default: break;
      }
      break;
    case Kind::EVAL_MUL:
      // TODO: allow mixed??
      switch (args[0]->d_tag)
      {
        case INTEGER:
          if (args[1]->d_tag==INTEGER)
          {
            return Literal(Integer(args[0]->d_int * args[1]->d_int));
          }
          break;
        case RATIONAL:
          if (args[1]->d_tag==RATIONAL)
          {
            return Literal(Rational(args[0]->d_rat * args[1]->d_rat));
          }
          break;
        default: break;
      }
      break;
    case Kind::EVAL_INT_DIV:
      if (args[0]->d_tag==INTEGER && args[1]->d_tag==INTEGER)
      {
        Integer& d = args[1]->d_int;
        if (d.sgn()!=0)
        {
          return Literal(Integer(args[0]->d_int.euclidianDivideQuotient(d)));
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
    case Kind::EVAL_TO_INT:
      switch (args[0]->d_tag)
      {
        case RATIONAL:return Literal(args[0]->d_rat.floor());
        default: break;
      }
      break;
    case Kind::EVAL_TO_RAT:
      switch (args[0]->d_tag)
      {
        case INTEGER:return Literal(Rational(args[0]->d_int));
        default: break;
      }
      break;
    default:break;
  }
  return Literal();
}

}  // namespace alfc

