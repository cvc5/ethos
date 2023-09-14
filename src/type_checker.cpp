#include "type_checker.h"

#include <iostream>
#include <set>
#include <unordered_map>

#include "base/check.h"
#include "base/output.h"
#include "state.h"
#include "parser.h"
#include "literal.h"

namespace alfc {
  
std::ostream& operator<<(std::ostream& out, const Ctx& c)
{
  out << "[";
  bool firstTime = true;
  for (const std::pair<ExprValue* const, ExprValue*>& cc : c)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << ", ";
    }
    out << Expr(cc.first) << " -> " << Expr(cc.second);
  }
  out << "]";
  return out;
}

TypeChecker::TypeChecker(State& s) : d_state(s)
{
  std::set<Kind> literalKinds = { Kind::BOOLEAN, Kind::NUMERAL,  Kind::DECIMAL, Kind::HEXADECIMAL, Kind::BINARY, Kind::STRING };
  // initialize literal kinds 
  for (Kind k : literalKinds)
  {
    d_literalTypeRules[k] = nullptr;
  }
}

TypeChecker::~TypeChecker()
{
}

void TypeChecker::setLiteralTypeRule(Kind k, const Expr& t)
{
  std::map<Kind, Expr>::iterator it = d_literalTypeRules.find(k);
  if (it==d_literalTypeRules.end())
  {
    std::stringstream ss;
    ALFC_FATAL() << "TypeChecker::setTypeRule: cannot set type rule for kind "
                 << k;
  }
  else if (it->second!=nullptr && it->second!=t)
  {
    std::stringstream ss;
    ALFC_FATAL() << "TypeChecker::setTypeRule: cannot set type rule for kind "
                 << k << " to " << t << ", since its type was already set to "
                 << it->second;
  }
  it->second = t;
}

ExprValue* TypeChecker::getOrSetLiteralTypeRule(Kind k)
{
  std::map<Kind, Expr>::iterator it = d_literalTypeRules.find(k);
  if (it==d_literalTypeRules.end())
  {
    std::stringstream ss;
    ALFC_FATAL() << "TypeChecker::getOrSetLiteralTypeRule: cannot get type rule for kind "
                 << k;
  }
  if (it->second==nullptr)
  {
    // If no type rule, assign the type rule to the builtin type
    Expr t = d_state.mkBuiltinType(k);
    d_literalTypeRules[k] = t;
    return t.getValue();
  }
  return it->second.getValue();
}

void TypeChecker::defineProgram(const Expr& v, const Expr& prog)
{
  d_programs[v.getValue()] = prog;
}

bool TypeChecker::hasProgram(const Expr& v) const
{
  return d_programs.find(v.getValue()) != d_programs.end();
}

Expr TypeChecker::getType(Expr& e, std::ostream* out)
{
  std::map<const ExprValue*, Expr>::iterator itt;
  std::unordered_set<ExprValue*> visited;
  std::vector<ExprValue*> toVisit;
  toVisit.push_back(e.getValue());
  ExprValue* cur;
  Expr ret;
  std::map<const ExprValue*, Expr>& tc = d_state.d_typeCache;
  do
  {
    cur = toVisit.back();
    itt = tc.find(cur);
    if (itt != tc.end())
    {
      ret = itt->second;
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
      ret = getTypeInternal(cur, out);
      if (ret.isNull())
      {
        // any subterm causes type checking to fail
        Trace("type_checker")
            << "TYPE " << Expr(cur) << " : [FAIL]" << std::endl;
        return ret;
      }
      tc[cur] = ret;
      Trace("type_checker")
          << "TYPE " << Expr(cur) << " : " << ret << std::endl;
      // std::cout << "...return" << std::endl;
      toVisit.pop_back();
    }
  }while (!toVisit.empty());
  return ret;
}

bool TypeChecker::checkArity(Kind k, size_t nargs)
{
  // check arities
  switch(k)
  {
    case Kind::NIL:
      return nargs==0;
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_TO_LIST:
    case Kind::EVAL_FROM_LIST:
    case Kind::EVAL_AND:
    case Kind::EVAL_OR:
    case Kind::EVAL_ADD:
    case Kind::EVAL_MUL:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_CONCAT:
    case Kind::EVAL_TO_BV:
      return nargs==2;
    case Kind::PROOF_TYPE:
    case Kind::EVAL_HASH:
    case Kind::EVAL_NOT:
    case Kind::EVAL_NEG:
    case Kind::EVAL_IS_NEG:
    case Kind::EVAL_IS_ZERO:
    case Kind::EVAL_LENGTH:
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_TO_RAT:
    case Kind::EVAL_TO_STRING:
      return nargs==1;
    case Kind::EVAL_REQUIRES:
    case Kind::EVAL_IF_THEN_ELSE:
    case Kind::EVAL_CONS:
    case Kind::EVAL_APPEND:
    case Kind::EVAL_EXTRACT:
      return nargs==3;
    default:break;
  }  
  return true;
}

Expr TypeChecker::getTypeInternal(ExprValue* e, std::ostream* out)
{
  Kind k = e->getKind();
  if (!checkArity(k, e->getNumChildren()))
  {
    (*out) << "Incorrect arity for " << k;
    return nullptr;
  }
  switch(k)
  {
    case Kind::APPLY:
    {
      return getTypeAppInternal(e->d_children, out);
    }
    case Kind::LAMBDA:
    {
      std::vector<Expr> args;
      std::vector<ExprValue*>& vars = e->d_children[0]->d_children;
      for (ExprValue* v : vars)
      {
        ExprValue* t = d_state.lookupType(v);
        Assert(t != nullptr);
        args.emplace_back(t);
      }
      Expr ret(d_state.lookupType(e->d_children[1]));
      Assert(!ret.isNull());
      return d_state.mkFunctionType(args, ret);
    }
    case Kind::NIL:
    case Kind::FAIL:
      // nil is its own type
      return e;
    case Kind::TYPE:
    case Kind::ABSTRACT_TYPE:
    case Kind::BOOL_TYPE:
    case Kind::FUNCTION_TYPE:
      return d_state.mkType();
    case Kind::PROOF_TYPE:
    {
      ExprValue* ctype = d_state.lookupType(e->d_children[0]);
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
    case Kind::QUOTE_TYPE:
      // anything can be quoted
      return d_state.mkType();
    case Kind::TUPLE:
      // not typed
      return d_state.mkAbstractType();
    case Kind::BOOLEAN:
      // note that Bool is builtin
      return d_state.mkBoolType();
    case Kind::NUMERAL:
    case Kind::DECIMAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING:
    {
      // use the literal type rule
      ExprValue* ret = getOrSetLiteralTypeRule(k);
      // it may involve the "self" parameter
      if (!ret->isGround())
      {
        Ctx ctx;
        ctx[d_state.mkSelf().getValue()] = e;
        return evaluateInternal(ret, ctx);
      }
      return ret;
    }
      break;
    default:
      // if a literal operator, consult auxiliary method
      if (isLiteralOp(k))
      {
        std::vector<ExprValue*> ctypes;
        std::vector<ExprValue*>& children = e->d_children;
        for (ExprValue* c : children)
        {
          ctypes.push_back(d_state.lookupType(c));
        }
        return getLiteralOpType(k, ctypes, out);
      }
      break;
  }
  if (out)
  {
    (*out) << "Unknown kind " << k;
  }
  return nullptr;
}

Expr TypeChecker::getTypeApp(std::vector<Expr>& children, std::ostream* out)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  return getTypeAppInternal(vchildren, out);
}

Expr TypeChecker::getTypeAppInternal(std::vector<ExprValue*>& children,
                                     std::ostream* out)
{
  Assert (!children.empty());
  ExprValue* hd = children[0];
  ExprValue* hdType = d_state.lookupType(hd);
  Assert(hdType != nullptr);
  if (hdType->getKind()!=Kind::FUNCTION_TYPE)
  {
    // non-function at head
    if (out)
    {
      (*out) << "Non-function " << Expr(hd) << " as head of APPLY";
    }
    return nullptr;
  }
  std::vector<ExprValue*> hdtypes = hdType->d_children;
  std::vector<ExprValue*> ctypes;
  if (hdtypes.size() != children.size())
  {
    // incorrect arity
    if (out)
    {
      (*out) << "Incorrect arity for " << Expr(hd)
             << ", #argTypes=" << hdtypes.size()
             << " #children=" << children.size();
    }
    return nullptr;
  }
  for (size_t i=1, nchild=children.size(); i<nchild; i++)
  {
    Assert (children[i]!=nullptr);
    // if the argument type is (Quote t), then we implicitly upcast
    // the argument c to (quote c). This is equivalent to matching
    // c to t directly, hence we take the child itself and not its
    // type.
    ExprValue* arg;
    if (hdtypes[i-1]->getKind()==Kind::QUOTE_TYPE)
    {
      // don't need to evaluate
      arg = children[i];
    }
    else
    {
      arg = d_state.lookupType(children[i]);
      Assert(arg != nullptr);
    }
    ctypes.emplace_back(arg);
  }
  // if compiled, run the compiled version of the type checker
  if (hdType->isCompiled())
  {
    Trace("type_checker") << "RUN type check " << Expr(hdType) << std::endl;
    return run_getTypeInternal(hdType, ctypes, out);
  }
  Ctx ctx;
  std::set<std::pair<ExprValue*, ExprValue*>> visited;
  for (size_t i=0, nchild=ctypes.size(); i<nchild; i++)
  {
    Assert(ctypes[i] != nullptr);
    // matching, update context
    ExprValue* hdt = hdtypes[i];
    // if the argument is (Quote t), we match on its argument,
    // which along with how ctypes[i] is the argument itself, has the effect
    // of an implicit upcast.
    hdt = hdt->getKind() == Kind::QUOTE_TYPE ? hdt->d_children[0] : hdt;
    if (!match(hdt, ctypes[i], ctx, visited))
    {
      if (out)
      {
        (*out) << "Unexpected argument type " << i << " of " << hd << std::endl;
        (*out) << "  LHS " << evaluateInternal(hdtypes[i], ctx) << ", from "
               << Expr(hdtypes[i]) << std::endl;
        (*out) << "  RHS " << Expr(ctypes[i]) << std::endl;
      }
      return nullptr;
    }
  }
  // evaluate in the matched context
  return evaluateInternal(hdtypes.back(), ctx);
}

bool TypeChecker::match(ExprValue* a, ExprValue* b, Ctx& ctx)
{
  std::set<std::pair<ExprValue*, ExprValue*>> visited;
  return match(a, b, ctx, visited);
}

bool TypeChecker::match(ExprValue* a,
                        ExprValue* b,
                        Ctx& ctx,
                        std::set<std::pair<ExprValue*, ExprValue*>>& visited)
{
  std::set<std::pair<ExprValue*, ExprValue*>>::iterator it;
  std::map<ExprValue*, ExprValue*>::iterator ctxIt;

  std::vector<std::pair<ExprValue*, ExprValue*>> stack;
  stack.emplace_back(a, b);
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
      if (curr.first->getKind() == Kind::PARAM)
      {
        // and we have not seen this variable before...
        ctxIt = ctx.find(curr.first);
        if (ctxIt == ctx.cend())
        {
          // note that we do not ensure the types match here
          // add the two subterms to `sub`
          ctx.emplace(curr.first, curr.second);
        }
        else if (ctxIt->second!=curr.second)
        {
          // if we saw this variable before, make sure that (now and before) it
          // maps to the same subterm
          return false;
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
  return evaluateInternal(e.getValue(), ctx);
}

Expr TypeChecker::evaluateInternal(ExprValue* e, Ctx& ctx)
{
  Assert (e!=nullptr);
  std::unordered_map<ExprValue*, Expr>::iterator it;
  Ctx::iterator itc;

  std::vector<std::unordered_map<ExprValue*, Expr>> visiteds;
  std::vector<Ctx> ctxs;
  std::vector<std::vector<ExprValue*>> visits;
  std::vector<ExprTrie*> ets;
  Expr evaluated;
  ExprValue* cur;
  ExprValue* init;
  visiteds.emplace_back();
  ctxs.emplace_back(ctx);
  visits.emplace_back(std::vector<ExprValue*>{e});
  Kind ck;
  while (!visits.empty())
  {
    std::unordered_map<ExprValue*, Expr>& visited = visiteds.back();
    std::vector<ExprValue*>& visit = visits.back();
    Ctx& cctx = ctxs.back();
    init = visit[0];
    while (!visit.empty())
    {
      cur = visit.back();
      Trace("type_checker_debug") << "visit " << cur << " " << cctx << ", depth=" << visits.size() << std::endl;
      // the term will stay the same if it is not evaluatable and either it
      // is ground, or the context is empty.
      if (!cur->isEvaluatable() && (cur->isGround() || cctx.empty()))
      {
        //std::cout << "...shortcut " << cur << std::endl;
        visited[cur] = cur;
        visit.pop_back();
        continue;
      }
      if (cur->getKind()==Kind::PARAM)
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
        // NOTE: this could be an error or warning, variable not filled
        //std::cout << "WARNING: unfilled variable " << cur << std::endl;
      }
      ck = cur->getKind();
      std::vector<ExprValue*>& children = cur->d_children;
      it = visited.find(cur);
      if (it == visited.end())
      {
        // if it is compiled, we run its evaluation here
        if (cur->isCompiled())
        {
          Trace("type_checker") << "RUN evaluate " << cur << std::endl;
          Expr retev = run_evaluate(cur, cctx);
          Assert (retev!=nullptr);
          if (retev!=nullptr)
          {
            Trace("type_checker") << "...returns " << retev << std::endl;
            visited[cur] = retev;
            visit.pop_back();
            continue;
          }
          // if we failed running via compiled, revert for now
          Trace("type_checker") << "...returns null" << std::endl;
        }
        // otherwise, visit children
        visited[cur] = Expr();
        if (ck==Kind::EVAL_IF_THEN_ELSE)
        {
          // special case: visit only the condition
          visit.push_back(children[0]);
        }
        else
        {
          visit.insert(visit.end(), children.begin(), children.end());
        }
        continue;
      }
      if (it->second.isNull())
      {
        std::vector<ExprValue*> cchildren;
        for (ExprValue* cp : children)
        {
          it = visited.find(cp);
          if (it != visited.end())
          {
            cchildren.push_back(it->second.getValue());
          }
          else
          {
            cchildren.push_back(nullptr);
          }
        }
        evaluated = Expr();
        bool newContext = false;
        bool canEvaluate = true;
        switch (ck)
        {
          case Kind::FAIL:
            // fail term means we immediately return
            return cur;
          case Kind::APPLY:
          {
            // if a program and all arguments are ground, run it
            Kind cck = cchildren[0]->getKind();
            if (cck==Kind::PROGRAM_CONST || cck==Kind::ORACLE)
            {
              // maybe already cached
              ExprTrie* et = &d_evalTrie;
              for (ExprValue* e : cchildren)
              {
                et = &(et->d_children[e]);
              }
              if (et->d_data!=nullptr)
              {
                evaluated = et->d_data;
              }
              else
              {
                Ctx newCtx;
                // see if we evaluate
                evaluated = evaluateProgramInternal(cchildren, newCtx);
                //std::cout << "Evaluate prog returned " << evaluated << std::endl;
                if (evaluated.isNull() || newCtx.empty())
                {
                  // if the evaluation can be shortcircuited, don't need to
                  // push a context
                  // store the base evaluation (if applicable)
                  et->d_data = evaluated.getValue();
                }
                else
                {
                  // otherwise push an evaluation scope
                  newContext = true;
                  ctxs.push_back(newCtx);
                  visits.emplace_back(
                      std::vector<ExprValue*>{evaluated.getValue()});
                  visiteds.emplace_back();
                  ets.push_back(et);
                }
              }
            }
          }
            break;
          case Kind::EVAL_IF_THEN_ELSE:
          {
            Assert (cchildren[0]!=nullptr);
            // get the evaluation of the condition
            const Literal* l = d_state.getLiteral(cchildren[0]);
            if (l!=nullptr && l->d_tag==Literal::BOOL)
            {
              // inspect the relevant child only
              size_t index = l->d_bool ? 1 : 2;
              if (cchildren[index] == nullptr)
              {
                canEvaluate = false;
                // evaluate the child if not yet done so
                visit.push_back(children[index]);
              }
              else
              {
                evaluated = cchildren[index];
              }
            }
            else
            {
              // note we must evaluate the children so that e.g. beta-reduction
              // and more generally substitution is accurate for non-ground
              // terms.
              for (size_t i=1; i<3; i++)
              {
                if (cchildren[i]==nullptr)
                {
                  // evaluate the child if not yet done so
                  visit.push_back(children[i]);
                  // can't evaluate yet if we aren't finished evaluating
                  canEvaluate = false;
                }
              }
            }
          }
            break;
          default:
            if (isLiteralOp(ck))
            {
              evaluated = evaluateLiteralOpInternal(ck, cchildren);
            }
            break;
        }
        if (newContext)
        {
          break;
        }
        if (canEvaluate)
        {
          if (evaluated.isNull())
          {
            evaluated = d_state.mkExprInternal(ck, cchildren);
          }
          visited[cur] = evaluated;
          visit.pop_back();
        }
      }
      else
      {
        visit.pop_back();
      }
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
        Trace("type_checker") << "EVALUATE " << Expr(init) << ", "
                              << ctxs.back() << " = " << evaluated << std::endl;
        visiteds.back()[visits.back().back()] = evaluated;
        visits.back().pop_back();
        // store the evaluation
        Assert(!ets.empty());
        ets.back()->d_data = evaluated.getValue();
        ets.pop_back();
      }
      ctxs.pop_back();
    }
  }
  Trace("type_checker") << "EVALUATE " << Expr(e) << ", " << ctx << " = "
                        << evaluated << std::endl;
  return evaluated;
}

Expr TypeChecker::evaluateProgram(const std::vector<Expr>& children, Ctx& newCtx)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  const Expr& ret = evaluateProgramInternal(vchildren, newCtx);
  if (!ret.isNull())
  {
    return ret;
  }
  // otherwise does not evaluate, return application
  return Expr(d_state.mkExprInternal(Kind::APPLY, vchildren));
}

bool TypeChecker::isGround(const std::vector<ExprValue*>& args)
{
  for (ExprValue* e : args)
  {
    if (!e->isGround())
    {
      return false;
    }
  }
  return true;
}

int run(const std::string& call, std::ostream& response)
{
  FILE* stream = popen(call.c_str(), "r");
  if (stream != nullptr)
  {
    int ch;
    while ((ch = fgetc(stream)) != EOF)
    {
      response << (unsigned char)ch;
    }
    return pclose(stream);
  }
  return -1;
}

Expr TypeChecker::evaluateProgramInternal(
    const std::vector<ExprValue*>& children, Ctx& newCtx)
{
  if (!isGround(children))
  {
    // do not evaluate on non-ground
    return nullptr;
  }
  ExprValue* hd = children[0];
  Kind hk = hd->getKind();
  if (hk==Kind::PROGRAM_CONST)
  {
    if (hd->isCompiled())
    {
      Trace("type_checker") << "RUN program " << children << std::endl;
      ExprValue* ret = run_evaluateProgram(children, newCtx);
      Trace("type_checker") << "...matches " << ret << ", ctx = " << newCtx << std::endl;
      return ret;
    }
    size_t nargs = children.size();
    std::map<ExprValue*, Expr>::iterator it = d_programs.find(hd);
    Assert (it!=d_programs.end());
    if (it!=d_programs.end())
    {
      Trace("type_checker") << "INTERPRET program " << children << std::endl;
      // otherwise, evaluate
      for (size_t i = 0, nchildren = it->second.getNumChildren(); i < nchildren;
           i++)
      {
        const Expr& c = it->second[i];
        newCtx.clear();
        ExprValue* hd = c[0].getValue();
        std::vector<ExprValue*>& hchildren = hd->d_children;
        if (nargs != hchildren.size())
        {
          // TODO: catch this during weak type checking of program bodies
          Warning() << "*** Bad number of arguments provided in function call to " << hd << std::endl;
          Warning() << "  Arguments: " << children << std::endl;
          return nullptr;
        }
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
          Trace("type_checker")
              << "...matches " << hd << ", ctx = " << newCtx << std::endl;
          return c[1].getValue();
        }
      }
      Trace("type_checker") << "...failed to match." << std::endl;
    }
  }
  else if (hk==Kind::ORACLE)
  {
    // get the command
    std::string ocmd;
    if (!d_state.getOracleCmd(hd, ocmd))
    {
      return nullptr;
    }
    std::stringstream call;
    call << ocmd;
    for (size_t i=1, nchildren=children.size(); i<nchildren; i++)
    {
      call << " " << Expr(children[i]);
    }
    Trace("oracles") << "Call oracle " << ocmd << " with arguments:" << std::endl;
    Trace("oracles") << "```" << std::endl;
    Trace("oracles") << call.str() << std::endl;
    Trace("oracles") << "```" << std::endl;
    std::stringstream response;
    int retVal = run(call.str(), response);
    if (retVal!=0)
    {
      Trace("oracles") << "...failed to run" << std::endl;
      return nullptr;
    }
    Trace("oracles") << "...got response \"" << response.str() << "\"" << std::endl;
    Parser poracle(d_state);
    poracle.setStringInput(response.str());
    Expr ret = poracle.parseNextExpr();
    Trace("oracles") << "returns " << ret << std::endl;
    return ret.getValue();
  }
  // just return nullptr, which should be interpreted as a failed evaluation
  return nullptr;
}

Expr TypeChecker::evaluateLiteralOp(Kind k, const std::vector<Expr>& args)
{
  std::vector<ExprValue*> vargs;
  for (const Expr& a : args)
  {
    vargs.push_back(a.getValue());
  }
  Expr ret = evaluateLiteralOpInternal(k, vargs);
  if (!ret.isNull())
  {
    return ret;
  }
  // otherwise does not evaluate, return application
  return Expr(d_state.mkExprInternal(k, vargs));
}

ExprValue* getNAryChildren(ExprValue* e,
                           ExprValue* op,
                           std::vector<ExprValue*>& children,
                           bool isLeft,
                           bool extractAll)
{
  while (e->getKind()==Kind::APPLY)
  {
    ExprValue* cop = (*e)[0];
    if (cop->getKind()!=Kind::APPLY)
    {
      break;
    }
    if ((*cop)[0] != op)
    {
      break;
    }
    // push back the element
    children.push_back(isLeft ? (*e)[1] : (*cop)[1]);
    // traverse to tail
    e = isLeft ? (*cop)[1] : (*e)[1];
    if (!extractAll && children.size()==2)
    {
      return e;
    }
  }
  // must be equal to the nil term
  return e;
}

Expr TypeChecker::evaluateLiteralOpInternal(Kind k,
                                            const std::vector<ExprValue*>& args)
{
  Trace("type_checker") << "EVALUATE-LIT " << k << " " << args << std::endl;
  switch (k)
  {
    case Kind::EVAL_IS_EQ:
    {
      Assert (args.size()==2);
      // evaluation is indepdent of whether it is a literal
      bool ret = args[0]==args[1];
      if (ret)
      {
        return d_state.mkTrue();
      }
      else if (isGround(args))
      {
        return d_state.mkFalse();
      }
      return nullptr;
    }
    break;
    case Kind::EVAL_IF_THEN_ELSE:
    {
      // temporary
      const Literal* l = d_state.getLiteral(args[0]);
      if (l!=nullptr && l->d_tag==Literal::BOOL)
      {
        return Expr(args[l->d_bool ? 1 : 2]);
      }
      /*
      // conditions equal
      if (args[1]==args[2])
      {
        return args[1];
      }
      */
      return nullptr;
    }
    break;
    case Kind::EVAL_REQUIRES:
    {
      if (args[0]==args[1])
      {
        return Expr(args[2]);
      }
      Trace("type_checker")
        << "REQUIRES: failed " << args[0] << " == " << args[1] << std::endl;
      return nullptr;
    }
    case Kind::EVAL_HASH:
    {
      if (args[0]->isGround())
      {
        size_t h = d_state.getHash(args[0]);
        return d_state.mkLiteralNumeral(h);
      }
      return nullptr;
    }
    case Kind::EVAL_CONS:
    case Kind::EVAL_APPEND:
    case Kind::EVAL_TO_LIST:
    case Kind::EVAL_FROM_LIST:
    {
      AppInfo* ac = d_state.getAppInfo(args[0]);
      Assert (ac!=nullptr);
      Attr ck = ac->d_attrCons;
      Assert (ck==Attr::RIGHT_ASSOC_NIL || ck==Attr::LEFT_ASSOC_NIL);
      bool isLeft = (ck==Attr::LEFT_ASSOC_NIL);
      Trace("type_checker_debug") << "CONS: " << isLeft << " " << args << std::endl;
      ExprValue* op = args[0];
      size_t tailIndex = (isLeft ? 1 : 2);
      size_t headIndex = (isLeft ? 2 : 1);
      // harg is either the head (cons/append) or the argument (to_list/from_list)
      ExprValue* harg = args[args.size() == 2 ? 1 : headIndex];
      if (!harg->isGround()) // or LIST?
      {
        // not ready
        Trace("type_checker_debug") << "...head is non-ground" <<std::endl;
        return d_null;
      }
      ExprValue* ret;
      std::vector<ExprValue*> hargs;
      switch (k)
      {
        case Kind::EVAL_TO_LIST:
        {
          if (harg == ac->d_attrConsTerm.getValue())
          {
            // already nil
            return Expr(harg);
          }
          ExprValue* a = harg;
          a = getNAryChildren(a, op, hargs, isLeft, false);
          if (!hargs.empty())
          {
            // already a list
            return Expr(harg);
          }
          // otherwise, turn into singleton list
          ret = ac->d_attrConsTerm.getValue();
          hargs.push_back(a);
        }
          break;
        case Kind::EVAL_FROM_LIST:
        {
          ExprValue* a = harg;
          a = getNAryChildren(a, op, hargs, isLeft, false);
          if (hargs.size()==1)
          {
            if (a != ac->d_attrConsTerm.getValue())
            {
              Warning() << "...failed to decompose " << harg << " in from_list" << std::endl;
              return nullptr;
            }
            // turn singleton list
            return hargs[0];
          }
          // otherwise self
          return Expr(harg);
        }
          break;
        case Kind::EVAL_CONS:
          ret = args[tailIndex];
          hargs.push_back(harg);
          break;
        case Kind::EVAL_APPEND:
        {
          ret = args[tailIndex];
          ExprValue* a = harg;
          // Note we take the tail verbatim
          a = getNAryChildren(a, op, hargs, isLeft, true);
          if (a != ac->d_attrConsTerm.getValue())
          {
            Warning() << "...failed to decompose " << harg << " in append" << std::endl;
            return nullptr;
          }
        }
          break;
        default:
          break;
      }
      std::vector<ExprValue*> cc;
      cc.push_back(op);
      cc.push_back(nullptr);
      cc.push_back(nullptr);
      for (size_t i=0, nargs=hargs.size(); i<nargs; i++)
      {
        cc[tailIndex] = ret;
        cc[headIndex] = hargs[isLeft ? i : (nargs-1-i)];
        ret = d_state.mkApplyInternal(cc);
      }
      Trace("type_checker_debug") << "CONS: " << isLeft << " " << args << " -> " << ret << std::endl;
      return ret;
    }
    default:
      break;
  }
  if (!isGround(args))
  {
    Trace("type_checker") << "...does not evaluate (non-ground)" << std::endl;
    return d_null;
  }
  // convert argument expressions to literals
  std::vector<const Literal*> lits;
  for (ExprValue* e : args)
  {
    const Literal* l = d_state.getLiteral(e);
    // symbols are stored as literals but do not evaluate
    if (l==nullptr || l->d_tag==Literal::SYMBOL)
    {
      Trace("type_checker") << "...does not evaluate (argument)" << std::endl;
      // failed to convert an argument
      return d_null;
    }
    lits.push_back(l);
  }
  // evaluate
  Literal eval = Literal::evaluate(k, lits);
  if (eval.d_tag==Literal::INVALID)
  {
    Trace("type_checker") << "...does not evaluate (return)" << std::endl;
    // failed to evaluate
    return d_null;
  }
  // convert back to an expression
  Expr lit = d_state.mkLiteral(eval.toKind(), eval.toString());
  Trace("type_checker") << "...evaluates to " << lit << std::endl;
  return lit;
}

ExprValue* TypeChecker::getLiteralOpType(Kind k,
                                         std::vector<ExprValue*>& childTypes,
                                         std::ostream* out)
{
  // NOTE: applications of most of these operators should only be in patterns,
  // where type checking is not strict.
  switch (k)
  {
    case Kind::EVAL_ADD:
    case Kind::EVAL_MUL:
    case Kind::EVAL_CONCAT:
    case Kind::EVAL_NEG:
      return childTypes[0];
    case Kind::EVAL_REQUIRES:
      return childTypes[2];
    case Kind::EVAL_IF_THEN_ELSE:
    case Kind::EVAL_CONS:
    case Kind::EVAL_APPEND:
    case Kind::EVAL_TO_LIST:
    case Kind::EVAL_FROM_LIST:
      return childTypes[1];
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_NOT:
    case Kind::EVAL_AND:
    case Kind::EVAL_OR:
    case Kind::EVAL_IS_NEG:
    case Kind::EVAL_IS_ZERO: return d_state.mkBoolType().getValue();
    case Kind::EVAL_HASH:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_LENGTH:
      return getOrSetLiteralTypeRule(Kind::NUMERAL);
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_TO_RAT:
      return getOrSetLiteralTypeRule(Kind::DECIMAL);
    default:break;
  }
  if (out)
  {
    (*out) << "Unknown type for literal operator " << k;
  }
  return nullptr;
}

}  // namespace alfc

