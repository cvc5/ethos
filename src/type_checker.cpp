#include "type_checker.h"

#include "state.h"
#include "error.h"
#include <iostream>
#include <set>
#include <unordered_map>

namespace atc {

TypeChecker::TypeChecker(State& s) : d_state(s)
{
  d_literalKinds = { Kind::INTEGER,  Kind::DECIMAL, Kind::HEXADECIMAL, Kind::BINARY, Kind::STRING };
  // initialize literal kinds 
  for (Kind k : d_literalKinds)
  {
    d_literalTypeRules[k] = d_state.mkBuiltinType(k);
  }
}

TypeChecker::~TypeChecker()
{
}

void TypeChecker::setTypeRule(Kind k, const Expr& e)
{
  std::map<Kind, Expr>::iterator it = d_literalTypeRules.find(k);
  if (it==d_literalTypeRules.end())
  {
    std::stringstream ss;
    ss << "TypeChecker::setTypeRule: cannot set type rule for kind " << k;
    Error::reportError(ss.str());
  }
  it->second = e;
}

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
  // TODO: check arities
  // TODO: non-recursive
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
      std::set<std::pair<Expr, Expr>> visited;
      for (size_t i=1, nchild=e->d_children.size(); i<nchild; i++)
      {
        Expr ctype = getType(e->d_children[i], out);
        if (ctype==nullptr)
        {
          return ctype;
        }
        // unification, update retType
        if (!match(hdtypes[i-1], ctype, ctx, visited))
        {
          out << "Unexpected argument type " << i << std::endl;
          out << "  LHS " << hdtypes[i-1] << std::endl;
          out << "  RHS " << ctype << std::endl;
          return nullptr;
        }
      }
      return evaluate(retType, ctx);
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
      return d_state.mkFunctionType(args, ret);
    }
    case Kind::QUOTE:
    {
      return d_state.mkQuoteType(e->d_children[0]);
    }
    case Kind::TYPE:
    case Kind::ABSTRACT_TYPE:
    case Kind::BOOL_TYPE:
      return d_state.mkType();
    case Kind::PROOF_TYPE:
    {
      Expr ctype = getType(e->d_children[0], out);
      if (ctype==nullptr)
      {
        return nullptr;
      }
      if (ctype->getKind()!=Kind::BOOL_TYPE)
      {
          out << "Non-Bool for argument of Proof";
        return nullptr;
      }
    }
      return d_state.mkType();
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
      return d_state.mkType();
    case Kind::REQUIRES_TYPE:
      for (size_t i=0, nreq = e->d_children.size()-1; i<nreq; i++)
      {
        if (e->d_children[i]->getKind()!=Kind::PAIR)
        {
          out << "Non-pair for requires";
          return nullptr;
        }
      }
      return d_state.mkType();
    case Kind::QUOTE_TYPE:
      // TODO: check arg?
      return d_state.mkType();
    case Kind::VARIABLE_LIST:
      return d_state.mkAbstractType();
    case Kind::INTEGER:
    case Kind::DECIMAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING:
      // use the literal type rule
      return d_literalTypeRules[e->getKind()];
    default:
      break;
  }
  out << "Unknown kind " << e->getKind();
  return nullptr;
}

bool TypeChecker::match(Expr& a, Expr& b, Ctx& ctx)
{
  std::set<std::pair<Expr, Expr>> visited;
  return match(a, b, ctx, visited);
}

bool TypeChecker::match(Expr& a, Expr& b, Ctx& ctx, std::set<std::pair<Expr, Expr>>& visited)
{
  std::set<std::pair<Expr, Expr>>::iterator it;
  std::map<Expr, Expr>::iterator ctxIt;

  std::vector<std::pair<Expr, Expr>> stack;
  stack.emplace_back(a, b);
  std::pair<Expr, Expr> curr;

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
        stack.emplace_back((*curr.first)[i], (*curr.second)[i]);
      }
    }
  }
  return true;
}

Expr TypeChecker::evaluate(Expr& e, Ctx& ctx)
{
  if (ctx.empty())
  {
    return e;
  }
  std::unordered_map<Expr, Expr> visited;
  std::unordered_map<Expr, Expr>::iterator it;
  std::vector<Expr> visit;
  Ctx::iterator itc;
  Expr evaluated;
  visit.push_back(e);
  Expr cur;
  while (!visit.empty())
  {
    cur = visit.back();
    // ground terms stay the same
    if (!cur->hasVariable())
    {
      visited[cur] = cur;
      visit.pop_back();
      continue;
    }
    if (cur->getKind()==Kind::VARIABLE)
    {
      // might be in context
      itc = ctx.find(cur);
      if (itc!=ctx.end())
      {
        visited[cur] = itc->second;
        visit.pop_back();
        continue;
      }
      // TODO: error, variable not filled?
    }
    std::vector<Expr>& children = cur->d_children;
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = nullptr;
      for (Expr& cp : children)
      {
        visit.push_back(cp);
      }
      continue;
    }
    visit.pop_back();
    if (it->second.get() == nullptr)
    {
      std::vector<Expr> cchildren;
      for (Expr& cp : children)
      {
        it = visited.find(cp);
        //Assert(it != visited.end());
        cchildren.push_back(it->second);
      }
      bool evaluatedSet = false;
      switch (cur->getKind())
      {
        case Kind::REQUIRES_TYPE:
        {
          // see if all requirements are met
          bool reqMet = true;
          for (size_t i=0, nreq = cchildren.size()-1; i<nreq; i++)
          {
            Expr req = cchildren[i];
            // Assert (p->getKind()==PAIR);
            if (!(*req.get())[0]->isEqual((*req.get())[1]))
            {
              reqMet = false;
              break;
            }
          }
          // If requirements are met, (requires ... T) evaluates to T.
          if (reqMet)
          {
            evaluated = cchildren.back();
            evaluatedSet = true;
          }
        }
          break;
        case Kind::APPLY:
          // maybe evaluate the program?
          evaluated = d_state.evaluate(cchildren);
          evaluatedSet = true;
          break;
        default:
          break;
      }
      if (!evaluatedSet)
      {
        evaluated = d_state.mkExpr(cur->getKind(), cchildren);
      }
      // remember its type
      evaluated->d_type = cur->d_type;
      visited[cur] = evaluated;
    }
  }
  //Assert(visited.find(this) != visited.end());
  return visited[e];
}

}  // namespace atc

