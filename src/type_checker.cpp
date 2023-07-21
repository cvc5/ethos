#include "type_checker.h"

#include "state.h"
#include "error.h"
#include <iostream>
#include <set>
#include <unordered_map>

namespace alfc {
  
std::ostream& operator<<(std::ostream& out, const Ctx& c)
{
  out << "[";
  bool firstTime = true;
  for (const std::pair<const Expr, Expr>& cc : c)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << ", ";
    }
    out << cc.first << " -> " << cc.second;
  }
  out << "]";
  return out;
}

TypeChecker::TypeChecker(State& s) : d_state(s)
{
  d_literalKinds = { Kind::INTEGER,  Kind::DECIMAL, Kind::HEXADECIMAL, Kind::BINARY, Kind::STRING };
  // initialize literal kinds 
  for (Kind k : d_literalKinds)
  {
    d_literalTypeRules[k] = nullptr;
  }
}

TypeChecker::~TypeChecker()
{
}

void TypeChecker::setTypeRule(Kind k, const Expr& t)
{
  std::map<Kind, Expr>::iterator it = d_literalTypeRules.find(k);
  if (it==d_literalTypeRules.end())
  {
    std::stringstream ss;
    ss << "TypeChecker::setTypeRule: cannot set type rule for kind " << k;
    Error::reportError(ss.str());
  }
  else if (it->second!=nullptr && it->second!=t)
  {
    std::stringstream ss;
    ss << "TypeChecker::setTypeRule: cannot set type rule for kind " << k << " to " << t << ", since its type was already set to " << it->second;
    Error::reportError(ss.str());
  }
  it->second = t;
}

Expr TypeChecker::getType(Expr& e, std::ostream& out)
{
  std::unordered_set<Expr> visited;
  std::vector<Expr> toVisit;
  toVisit.push_back(e);
  Expr cur;
  do
  {
    cur = toVisit.back();
    if (cur->d_type!=nullptr)
    {
      // already computed type
      toVisit.pop_back();
      continue;
    }
    if (visited.find(cur)==visited.end())
    {
      visited.insert(cur);
      toVisit.insert(toVisit.end(), cur->d_children.begin(), cur->d_children.end());
    }
    else
    {
      cur->d_type = getTypeInternal(cur, out);
      if (cur->d_type==nullptr)
      {
        // any subterm causes type checking to fail
        return nullptr;
      }
      toVisit.pop_back();
    }
  }while (!toVisit.empty());
  return e->d_type;
}

Expr TypeChecker::getTypeInternal(Expr& e, std::ostream& out)
{
  // TODO: check arities
  // TODO: don't need to check child nullptr?
  switch(e->getKind())
  {
    case Kind::APPLY:
    {
      Expr hdType = e->d_children[0]->d_type;
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
        Expr ctype = e->d_children[i]->d_type;
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
        Expr ctype = c->d_type;
        if (ctype==nullptr)
        {
          return ctype;
        }
        args.push_back(ctype);
      }
      Expr ret = e->d_children[1]->d_type;
      if (ret==nullptr)
      {
        return ret;
      }
      return d_state.mkFunctionType(args, ret);
    }
    case Kind::QUOTE:
      // (quote t) : (Quote t)
      return d_state.mkQuoteType(e->d_children[0]);
    case Kind::TYPE:
    case Kind::ABSTRACT_TYPE:
    case Kind::BOOL_TYPE:
      return d_state.mkType();
    case Kind::PROOF_TYPE:
    {
      Expr ctype = e->d_children[0]->d_type;
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
        Expr ctype = c->d_type;
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
      // anything can be quoted
      return d_state.mkType();
    case Kind::VARIABLE_LIST:
      return d_state.mkAbstractType();
    case Kind::INTEGER:
    case Kind::DECIMAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING:
    {
      Kind k = e->getKind();
      // use the literal type rule
      Expr t = d_literalTypeRules[k];
      if (t==nullptr)
      {
        t = d_state.mkBuiltinType(k);
        d_literalTypeRules[k] = t;
      }
      return t;
    }
      break;
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

Expr TypeChecker::evaluate(Expr& e)
{
  Ctx ctx;
  return evaluate(e, ctx);
}
  
Expr TypeChecker::evaluate(Expr& e, Ctx& ctx)
{
  std::unordered_map<Expr, Expr>::iterator it;
  Ctx::iterator itc;
  
  std::vector<std::unordered_map<Expr, Expr>> visiteds;
  std::vector<Ctx> ctxs;
  std::vector<std::vector<Expr>> visits;
  Expr evaluated;
  Expr cur;
  Expr init;
  visiteds.emplace_back();
  ctxs.emplace_back(ctx);
  visits.emplace_back(std::vector<Expr>{e});
  while (!visits.empty())
  {
    std::unordered_map<Expr, Expr>& visited = visiteds.back();
    std::vector<Expr>& visit = visits.back();
    Ctx& cctx = ctxs.back();
    init = visit[0];
    while (!visit.empty())
    {
      cur = visit.back();
      // unevaluatable terms stay the same
      if (!cur->isEvaluatable())
      {
        visited[cur] = cur;
        visit.pop_back();
        continue;
      }
      if (cur->getKind()==Kind::VARIABLE)
      {
        // might be in context
        itc = cctx.find(cur);
        if (itc!=cctx.end())
        {
          visited[cur] = itc->second;
          visit.pop_back();
          continue;
        }
        // TODO: error, variable not filled?
        //std::cout << "WARNING: unfilled variable " << cur << std::endl;
      }
      std::vector<Expr>& children = cur->d_children;
      it = visited.find(cur);
      if (it == visited.end())
      {
        visited[cur] = nullptr;
        visit.insert(visit.end(), children.begin(), children.end());
        continue;
      }
      if (it->second.get() == nullptr)
      {
        std::vector<Expr> cchildren;
        for (Expr& cp : children)
        {
          it = visited.find(cp);
          //Assert(it != visited.end());
          cchildren.push_back(it->second);
        }
        evaluated = nullptr;
        bool newContext = false;
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
            }
          }
            break;
          case Kind::APPLY:
            // maybe evaluate the program?
            if (cchildren[0]->getKind()==Kind::PROGRAM_CONST)
            {
              ctxs.emplace_back();
              // see if we evaluate 
              evaluated = d_state.evaluate(cchildren, ctxs.back());
              if (ctxs.back().empty())
              {
                // if there is no context, we don't have to push a scope
                ctxs.pop_back();
              }
              else
              {
                // otherwise push an evaluation scope
                newContext = true;
                visits.emplace_back(std::vector<Expr>{evaluated});
                visiteds.emplace_back();
              }
            }
            break;
          default:
            break;
        }
        if (newContext)
        {
          break;
        }
        if (evaluated==nullptr)
        {
          evaluated = d_state.mkExpr(cur->getKind(), cchildren);
        }
        // remember its type
        evaluated->d_type = cur->d_type;
        visited[cur] = evaluated;
      }
      visit.pop_back();
    }
    // if we are done evaluating the current context
    if (visits.back().empty())
    {
      // get the result from the inner evaluation
      evaluated = visiteds.back()[init];
      // pop the evaluation context
      visiteds.pop_back();
      visits.pop_back();
      // set the result
      if (!visits.empty())
      {
        std::cout << "EVALUATE " << visits.back().back() << ", " << ctxs.back() << " = " << evaluated << std::endl;
        visiteds.back()[visits.back().back()] = evaluated;
        visits.back().pop_back();
      }
      ctxs.pop_back();
    }
  }
  std::cout << "EVALUATE " << e << ", " << ctx << " = " << evaluated << std::endl;
  //Assert(visited.find(this) != visited.end());
  return evaluated;
}

}  // namespace alfc

