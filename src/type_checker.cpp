#include "type_checker.h"

#include "state.h"
#include <iostream>

namespace atc {

Expr TypeChecker::getType(Expr& e, std::ostream& out)
{
  if (e->d_type==nullptr)
  {
    e->d_type = getTypeInternal(e, out);
  }
  return e->d_type;
}

Expr TypeChecker::getTypeInternal(Expr& e, std::ostream& out)
{
  switch(e->getKind())
  {
    case Kind::APPLY:
    {
      Expr hdType = getType(e->d_children[0], out);
      if (hdType==nullptr)
      {
        return hdType;
      }
      std::vector<Expr> expectedTypes;
      if (hdType->getKind()!=Kind::FUNCTION_TYPE)
      {
        // non-function at head
        out << "Non-function as head of APPLY";
        return nullptr;
      }
      const std::vector<Expr>& hdtypes = hdType->getChildren();
      if (hdtypes.size()!=e->d_children.size())
      {
        // incorrect arity
        out << "Incorrect arity";
        return nullptr;
      }
      Expr retType = hdtypes.back();
      Ctx ctx;
      for (size_t i=1, nchild=e->d_children.size(); i<nchild; i++)
      {
        Expr ctype = getType(e->d_children[i], out);
        if (ctype==nullptr)
        {
          return ctype;
        }
        // unification, update retType
        if (!hdtypes[i-1]->match(ctype, ctx))
        {
          out << "Unexpected argument type " << i << std::endl;
          out << "  LHS " << hdtypes[i-1] << std::endl;
          out << "  RHS " << ctype << std::endl;
          return nullptr;
        }
      }
      if (ctx.empty())
      {
        return retType;
      }
      return retType->clone(ctx);
    }
    case Kind::LAMBDA:
    {
      std::vector<Expr> args;
      std::vector<Expr>& vars = e->d_children[0]->d_children;
      for (Expr& c : vars)
      {
        Expr ctype = getType(c, out);
        if (ctype==nullptr)
        {
          return ctype;
        }
        args.push_back(ctype);
      }
      Expr ret = getType(e->d_children[1], out);
      if (ret==nullptr)
      {
        return ret;
      }
      return ExprValue::d_state->mkFunctionType(args, ret);
    }
    case Kind::QUOTE:
    {
      return ExprValue::d_state->mkQuoteType(e->d_children[0]);
    }
    case Kind::TYPE:
    case Kind::ABSTRACT_TYPE:
    case Kind::PROOF_TYPE:
    case Kind::BOOL_TYPE:
      return ExprValue::d_state->mkType();
    case Kind::FUNCTION_TYPE:
      // the children must be types
      for (Expr& c : e->d_children)
      {
        Expr ctype = getType(c, out);
        if (ctype==nullptr)
        {
          return ctype;
        }
        if (ctype->getKind()!=Kind::TYPE)
        {
          out << "Non-type for function";
          return nullptr;
        }
      }
      return ExprValue::d_state->mkType();
    case Kind::QUOTE_TYPE:
      // TODO: check arg?
      return ExprValue::d_state->mkType();
    case Kind::VARIABLE_LIST:
    case Kind::INTEGER:
    case Kind::DECIMAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING:
      return ExprValue::d_state->mkBuiltinType(e->getKind());
    default:
      break;
  }
  out << "Unknown kind " << e->getKind();
  return nullptr;
}


}  // namespace atc

