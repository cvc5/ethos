#include "type_checker.h"

#include <iostream>
#include <set>
#include <unordered_map>

#include "base/check.h"
#include "error.h"
#include "state.h"

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

std::ostream& operator<<(std::ostream& out, const std::vector<Expr>& children)
{
  out << "[";
  bool firstTime = true;
  for (const Expr& e : children)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << ", ";
    }
    out << e;
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
  Assert(t->isGround());
  it->second = t;
}

void TypeChecker::defineProgram(const Expr& v, const Expr& prog)
{
  d_programs[v] = prog;
}

bool TypeChecker::hasProgram(const Expr& v) const
{
  return d_programs.find(v)!=d_programs.end();
}

const Expr& TypeChecker::getType(Expr& e, std::ostream* out)
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
      //std::cout << "Type check " << cur << std::endl;
      cur->d_type = getTypeInternal(cur, out);
      //std::cout << "...return" << std::endl;
      if (cur->d_type==nullptr)
      {
        // any subterm causes type checking to fail
        Assert(e->d_type == nullptr);
        return e->d_type;
      }
      toVisit.pop_back();
    }
  }while (!toVisit.empty());
  return e->d_type;
}

Expr TypeChecker::getTypeInternal(Expr& e, std::ostream* out)
{
  // TODO: check arities
  switch(e->getKind())
  {
    case Kind::APPLY:
    {
      std::vector<Expr>& children = e->d_children;
      Expr& hd = children[0];
      Expr hdType = hd->d_type;
      Assert(hdType != nullptr);
      if (hdType->getKind()!=Kind::FUNCTION_TYPE)
      {
        // non-function at head
        if (out)
        {
          (*out) << "Non-function as head of APPLY";
        }
        return nullptr;
      }
      std::vector<Expr>& hdtypes = hdType->d_children;
      std::vector<Expr> ctypes;
      for (size_t i=1, nchild=children.size(); i<nchild; i++)
      {
        // if the argument type is (Quote t), then we implicitly upcast
        // the argument c to (quote c). This is equivalent to matching
        // c to t directly, hence we take the child itself and not its
        // type.
        if (hdtypes[i-1]->getKind()==Kind::QUOTE_TYPE)
        {
          ctypes.push_back(evaluate(children[i]));
        }
        else
        {
          ctypes.push_back(children[i]->d_type);
        }
      }
      if (hdtypes.size()!=children.size())
      {
        // incorrect arity
        if (out)
        {
          (*out) << "Incorrect arity, #argTypes=" << hdtypes.size() << " #children=" << children.size();
        }
        return nullptr;
      }
      // if compiled, run the compiled version of the type checker
      if (hdType->isCompiled())
      {
        std::cout << "RUN type check " << hdType << std::endl;
        return run_getTypeInternal(hdType, ctypes, out);
      }
      Ctx ctx;
      std::set<std::pair<Expr, Expr>> visited;
      for (size_t i=0, nchild=ctypes.size(); i<nchild; i++)
      {
        Assert(ctypes[i] != nullptr);
        // matching, update context
        Expr hdt = hdtypes[i];
        // if the argument is (Quote t), we match on its argument,
        // which along with how ctypes[i] is the argument itself, has the effect
        // of an implicit upcast.
        hdt = hdt->getKind()==Kind::QUOTE_TYPE ? hdt->getChildren()[0] : hdt;
        if (!match(hdt, ctypes[i], ctx, visited))
        {
          if (out)
          {
            (*out) << "Unexpected argument type " << i << std::endl;
            (*out) << "  LHS " << hdtypes[i] << std::endl;
            (*out) << "  RHS " << ctypes[i] << std::endl;
          }
          return nullptr;
        }
      }
      // evaluate in the matched context
      return evaluate(hdtypes.back(), ctx);
    }
    case Kind::LAMBDA:
    {
      std::vector<Expr> args;
      std::vector<Expr>& vars = e->d_children[0]->d_children;
      for (Expr& c : vars)
      {
        Assert(c->d_type != nullptr);
        args.push_back( c->d_type);
      }
      Expr ret = e->d_children[1]->d_type;
      Assert(ret != nullptr);
      return d_state.mkFunctionType(args, ret);
    }
    case Kind::QUOTE:
    {
      // (quote t) : (Quote t)
      // evaluate t here if ground/evaluatable
      if (e->d_children[0]->isGround())
      {
        Expr t = e->d_children[0];
        return d_state.mkQuoteType(evaluate(t));
      }
      return d_state.mkQuoteType(e->d_children[0]);
    }
    case Kind::NIL:
    {
      // type stored as the child
      return e->d_children[0];
    }
    case Kind::TYPE:
    case Kind::ABSTRACT_TYPE:
    case Kind::BOOL_TYPE:
    case Kind::FUNCTION_TYPE:
      return d_state.mkType();
    case Kind::PROOF_TYPE:
    {
      const Expr& ctype = e->d_children[0]->d_type;
      Assert(ctype != nullptr);
      if (ctype->getKind()!=Kind::BOOL_TYPE)
      {
        if (out)
        {
          (*out) << "Non-Bool for argument of Proof";
        }
        return nullptr;
      }
    }
      return d_state.mkType();
    case Kind::REQUIRES_TYPE:
      for (size_t i=0, nreq = e->d_children.size()-1; i<nreq; i++)
      {
        if (e->d_children[i]->getKind()!=Kind::PAIR)
        {
          if (out)
          {
            (*out) << "Non-pair for requires";
          }
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
        // If no type rule, assign the type rule to the builtin type
        t = d_state.mkBuiltinType(k);
        d_literalTypeRules[k] = t;
      }
      return t;
    }
      break;
    default:
      break;
  }
  if (out)
  {
    (*out) << "Unknown kind " << e->getKind();
  }
  return nullptr;
}

bool TypeChecker::match(const Expr& a, const Expr& b, Ctx& ctx)
{
  std::set<std::pair<Expr, Expr>> visited;
  return match(a, b, ctx, visited);
}

bool TypeChecker::match(const Expr& a, const Expr& b, Ctx& ctx, std::set<std::pair<Expr, Expr>>& visited)
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
  std::vector<ExprTrie*> ets;
  Expr evaluated;
  Expr cur;
  Expr init;
  visiteds.emplace_back();
  ctxs.emplace_back(ctx);
  visits.emplace_back(std::vector<Expr>{e});
  Kind ck;
  while (!visits.empty())
  {
    std::unordered_map<Expr, Expr>& visited = visiteds.back();
    std::vector<Expr>& visit = visits.back();
    Ctx& cctx = ctxs.back();
    init = visit[0];
    while (!visit.empty())
    {
      cur = visit.back();
      //std::cout << "visit " << cur << " " << cctx << std::endl;
      // the term will stay the same if it is not evaluatable and either it
      // is ground, or the context is empty.
      if (!cur->isEvaluatable() && (cur->isGround() || cctx.empty()))
      {
        //std::cout << "...shortcut " << cur << std::endl;
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
        visited[cur] = cur;
        visit.pop_back();
        continue;
        // NOTE: this could be an error or warning, variable not filled?
        //std::cout << "WARNING: unfilled variable " << cur << std::endl;
      }
      std::vector<Expr>& children = cur->d_children;
      it = visited.find(cur);
      if (it == visited.end())
      {
        // if it is compiled, we run its evaluation here
        if (cur->isCompiled())
        {
          std::cout << "RUN evaluate " << cur << std::endl;
          visited[cur] = run_evaluate(cur, cctx);
          visit.pop_back();
          continue;
        }
        // otherwise, visit children
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
          Assert(it != visited.end());
          cchildren.push_back(it->second);
        }
        evaluated = nullptr;
        bool newContext = false;
        ck = cur->getKind();
        switch (ck)
        {
          case Kind::REQUIRES_TYPE:
          {
            // see if all requirements are met
            bool reqMet = true;
            for (size_t i=0, nreq = cchildren.size()-1; i<nreq; i++)
            {
              Expr& req = cchildren[i];
              Assert(req->getKind() == Kind::PAIR);
              Expr e1 = (*req.get())[0];
              Expr e2 = (*req.get())[1];
              if (!e1->isEqual(e2))
              {
                reqMet = false;
                std::cout << "REQUIRES: failed " << e1 << " == " << e2 << std::endl;
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
              // maybe already cached
              ExprTrie* et = &d_evalTrie;
              for (const Expr& e : cchildren)
              {
                et = &(et->d_children[e.get()]);
              }
              if (et->d_data!=nullptr)
              {
                evaluated = et->d_data;
              }
              else
              {
                ctxs.emplace_back();
                // see if we evaluate
                evaluated = evaluateProgram(cchildren, ctxs.back());
                //std::cout << "Evaluate prog returned " << evaluated << std::endl;
                if (evaluated==nullptr || ctxs.back().empty())
                {
                  // if the evaluation can be shortcircuited, don't need to
                  // push a context
                  ctxs.pop_back();
                  // get the reference to the back of the vector again, which
                  // may have changed.
                  cctx = ctxs.back();
                  // store the base evaluation (if applicable)
                  et->d_data = evaluated;
                }
                else
                {
                  // otherwise push an evaluation scope
                  newContext = true;
                  visits.emplace_back(std::vector<Expr>{evaluated});
                  visiteds.emplace_back();
                  ets.push_back(et);
                }
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
          evaluated = d_state.mkExprInternal(ck, cchildren);
        }
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
        std::cout << "EVALUATE " << init << ", " << ctxs.back() << " = " << evaluated << std::endl;
        visiteds.back()[visits.back().back()] = evaluated;
        visits.back().pop_back();
        // store the evaluation
        Assert(!ets.empty());
        ets.back()->d_data = evaluated;
        ets.pop_back();
      }
      ctxs.pop_back();
    }
  }
  std::cout << "EVALUATE " << e << ", " << ctx << " = " << evaluated << std::endl;
  return evaluated;
}

Expr TypeChecker::evaluateProgram(const std::vector<Expr>& children, Ctx& newCtx)
{
  const Expr& hd = children[0];
  if (hd->isCompiled())
  {
    std::cout << "RUN program " << children << std::endl;
    return run_evaluateProgram(children, newCtx);
  }
  std::map<Expr, Expr>::iterator it = d_programs.find(hd);
  if (it!=d_programs.end())
  {
    std::cout << "INTERPRET program " << children << std::endl;
    // otherwise, evaluate
    std::vector<Expr>& progChildren = it->second->getChildren();
    size_t nargs = children.size();
    for (Expr& c : progChildren)
    {
      newCtx.clear();
      Expr hd = c->getChildren()[0];
      std::vector<Expr>& hchildren = hd->d_children;
      Assert(nargs == hchildren.size());
      bool matchSuccess = true;
      for (size_t i=1; i<nargs; i++)
      {
        if (!match(hchildren[i], children[i], newCtx))
        {
          matchSuccess = false;
          break;
        }
      }
      if (matchSuccess)
      {
        std::cout << "...matches " << hd << ", ctx = " << newCtx << std::endl;
        return c->getChildren()[1];
      }
    }
  }
  // just return nullptr, which should be interpreted as a failed evaluation
  return nullptr;
}

}  // namespace alfc

