#include "type_checker.h"

#include "state.h"
#include <iostream>
#include <set>

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
      std::vector<Expr>& hdtypes = hdType->d_children;
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
        if (!match(hdtypes[i-1], ctype, ctx))
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


bool TypeChecker::match(Expr& a, Expr& b, Ctx& ctx)
{
  std::set<std::pair<ExprValue*, ExprValue*>> visited;
  std::set<std::pair<ExprValue*, ExprValue*>>::iterator it;
  std::map<ExprValue*, ExprValue*>::iterator ctxIt;

  std::vector<std::pair<ExprValue*, ExprValue*>> stack;
  stack.emplace_back(a.get(), b.get());
  std::pair<ExprValue*, ExprValue*> curr;

  while (!stack.empty())
  {
    curr = stack.back();
    stack.pop_back();
    if (curr.first == curr.second)
    {
      // holds trivially
      continue;
    }
    it = visited.find(curr);
    if (it != visited.end())
    {
      // already processed
      continue;
    }
    visited.insert(curr);
    if (curr.first->getNumChildren() == 0)
    {
      // if the two subterms are not equal and the first one is a bound
      // variable...
      if (curr.first->getKind() == Kind::VARIABLE)
      {
        // and we have not seen this variable before...
        ctxIt = ctx.find(curr.first);
        if (ctxIt == ctx.cend())
        {
          // TODO: ensure types are the same?
          // add the two subterms to `sub`
          ctx.emplace(curr.first, curr.second);
        }
        else
        {
          // if we saw this variable before, make sure that (now and before) it
          // maps to the same subterm
          stack.emplace_back(ctxIt->second, curr.second);
        }
      }
      else
      {
        // the two subterms are not equal
        return false;
      }
    }
    else
    {
      // if the two subterms are not equal, make sure that their operators are
      // equal
      if (curr.first->getNumChildren() != curr.second->getNumChildren()
          || curr.first->getKind() != curr.second->getKind())
      {
        return false;
      }
      // recurse on children
      for (size_t i = 0, n = curr.first->getNumChildren(); i < n; ++i)
      {
        stack.emplace_back((*curr.first)[i].get(), (*curr.second)[i].get());
      }
    }
  }
  return true;
}


}  // namespace atc

