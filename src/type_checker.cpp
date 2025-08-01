/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "type_checker.h"

#include <iostream>
#include <set>
#include <unordered_map>

#include "base/check.h"
#include "base/output.h"
#include "expr.h"
#include "literal.h"
#include "parser.h"
#include "state.h"

namespace ethos {

TypeChecker::TypeChecker(State& s, Options& opts) : d_state(s), d_plugin(nullptr), d_sts(s.getStats())
{
  std::set<Kind> literalKinds = { Kind::BOOLEAN, Kind::NUMERAL, Kind::RATIONAL, Kind::BINARY, Kind::STRING, Kind::DECIMAL, Kind::HEXADECIMAL };
  // initialize literal kinds 
  for (Kind k : literalKinds)
  {
    d_literalTypeRules[k] = d_null;
  }
  d_statsEnabled = opts.d_stats;
}

TypeChecker::~TypeChecker()
{
}

void TypeChecker::setLiteralTypeRule(Kind k, const Expr& t)
{
  Trace("type_checker") << "**** setLiteralTypeRule " << k << " to " << t
                        << std::endl;
  std::map<Kind, Expr>::iterator it = d_literalTypeRules.find(k);
  if (it==d_literalTypeRules.end())
  {
    std::stringstream ss;
    EO_FATAL() << "TypeChecker::setTypeRule: cannot set type rule for kind "
                 << k;
  }
  else if (!it->second.isNull() && it->second != t)
  {
    std::stringstream ss;
    EO_FATAL() << "TypeChecker::setTypeRule: cannot set type rule for kind "
                 << k << " to " << t << ", since its type was already set to "
                 << it->second;
  }
  it->second = t;
}

Expr TypeChecker::getOrSetLiteralTypeRule(Kind k, ExprValue* self)
{
  std::map<Kind, Expr>::iterator it = d_literalTypeRules.find(k);
  if (it==d_literalTypeRules.end())
  {
    std::stringstream ss;
    EO_FATAL() << "TypeChecker::getOrSetLiteralTypeRule: cannot get type rule for kind "
                 << k;
  }
  Expr tp;
  if (it->second.isNull())
  {
    // If no type rule, assign the type rule to the builtin type
    tp = d_state.mkBuiltinType(k);
    d_literalTypeRules[k] = tp;
  }
  else
  {
    tp = it->second;
  }
  // it may involve the "self" parameter
  if (!tp.isGround())
  {
    Expr eself = self == nullptr ? d_state.mkAny() : Expr(self);
    Ctx ctx;
    ctx[d_state.mkSelf().getValue()] = eself.getValue();
    return evaluate(tp.getValue(), ctx);
  }
  return tp;
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
      if (ret.isGround() && ret.isEvaluatable())
      {
        Trace("type_checker")
            << "TYPE " << Expr(cur) << " : [FAIL] due to evaluatable " << ret << std::endl;
        if (out)
        {
          (*out) << "Has type " << ret << " whose evaluation cannot be reduced";
        }
        return d_null;
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

bool TypeChecker::checkArity(Kind k, size_t nargs, std::ostream* out)
{
  bool ret = false;
  // check arities
  switch(k)
  {
    case Kind::ANNOT_PARAM:
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_VAR:
    case Kind::EVAL_EQ:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_INT_MOD:
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_TO_BIN:
    case Kind::EVAL_FIND:
    case Kind::EVAL_COMPARE:
    case Kind::EVAL_GT:
    case Kind::EVAL_LIST_LENGTH:
    case Kind::EVAL_LIST_REV:
    case Kind::EVAL_LIST_SETOF: ret = (nargs == 2); break;
    case Kind::EVAL_NIL:
      ret = (nargs==2);
      break;
    case Kind::EVAL_LIST_CONCAT: ret = (nargs == 3); break;
    case Kind::PROOF_TYPE:
    case Kind::EVAL_IS_OK:
    case Kind::EVAL_TYPE_OF:
    case Kind::EVAL_NAME_OF:
    case Kind::EVAL_HASH:
    case Kind::EVAL_NOT:
    case Kind::EVAL_NEG:
    case Kind::EVAL_IS_NEG:
    case Kind::EVAL_LENGTH:
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_TO_RAT:
    case Kind::EVAL_TO_STRING:
    case Kind::EVAL_IS_Z:
    case Kind::EVAL_IS_Q:
    case Kind::EVAL_IS_BIN:
    case Kind::EVAL_IS_STR:
    case Kind::EVAL_IS_BOOL:
    case Kind::EVAL_IS_VAR:
    case Kind::EVAL_DT_CONSTRUCTORS:
    case Kind::EVAL_DT_SELECTORS: ret = (nargs == 1); break;
    case Kind::EVAL_REQUIRES:
    case Kind::EVAL_IF_THEN_ELSE:
    case Kind::EVAL_CONS:
    case Kind::EVAL_LIST_FIND:
    case Kind::EVAL_LIST_ERASE:
    case Kind::EVAL_LIST_ERASE_ALL:
    case Kind::EVAL_LIST_NTH:
    case Kind::EVAL_LIST_MINCLUDE:
    case Kind::EVAL_LIST_MEQ:
    case Kind::EVAL_LIST_DIFF:
    case Kind::EVAL_LIST_INTER: ret = (nargs == 3); break;
    case Kind::EVAL_EXTRACT:
      ret = (nargs==3 || nargs==2);
      break;
    default:
      if (isNaryLiteralOp(k))
      {
        ret = (nargs == 2);
      }
      else if (out)
      {
        (*out) << "Unknown arity for " << k;
      }
      break;
  }
  if (!ret)
  {
    if (out)
    {
      (*out) << "Incorrect arity for " << k;
    }
    return false;
  }
  return true;
}

Expr TypeChecker::getTypeInternal(ExprValue* e, std::ostream* out)
{
  Kind k = e->getKind();
  switch(k)
  {
    case Kind::APPLY:
    case Kind::APPLY_OPAQUE:
    {
      Ctx ctx;
      return getTypeAppInternal(e->d_children, ctx, out);
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
    case Kind::TYPE:
    case Kind::BOOL_TYPE:
    case Kind::FUNCTION_TYPE:
    case Kind::PROGRAM_TYPE:
    case Kind::ANY: return d_state.mkType();
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
        return d_null;
      }
    }
      return d_state.mkType();
    case Kind::ANNOT_PARAM:
      // its type is the second child
      return Expr(e->d_children[1]);
    case Kind::QUOTE_TYPE:
    case Kind::TUPLE:
      // These things are essentially not typed.
      // We require the first 3 to be an abstract type, not type,
      // to prevent them from being used as (return) types of terms.
      return d_state.mkAny();
    case Kind::BOOLEAN:
      // note that Bool is builtin
      return d_state.mkBoolType();
    case Kind::NUMERAL:
    case Kind::DECIMAL:
    case Kind::RATIONAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING:
    {
      // use the literal type rule
      return getOrSetLiteralTypeRule(k, e);
    }
      break;
    case Kind::AS:
    case Kind::AS_RETURN:
    {
      // constructing an application of AS means the type was incorrect.
      if (out)
      {
        (*out) << "Encountered bad type for " << kindToTerm(k);
      }
      return d_null;
    }
      break;
    case Kind::PARAMETERIZED:
    {
      // type of the second child
      return Expr(d_state.lookupType(e->d_children[1]));
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
        return getLiteralOpType(k, children, ctypes, out);
      }
      break;
  }
  if (out)
  {
    (*out) << "Unknown kind " << k;
  }
  return d_null;
}

Expr TypeChecker::getTypeApp(std::vector<Expr>& children, std::ostream* out)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  Ctx ctx;
  return getTypeAppInternal(vchildren, ctx, out);
}

Expr TypeChecker::getTypeAppInternal(std::vector<ExprValue*>& children,
                                     Ctx& ctx,
                                     std::ostream* out)
{
  Assert (!children.empty());
  ExprValue* hd = children[0];
  ExprValue* hdType = d_state.lookupType(hd);
  Assert(hdType != nullptr) << "No type for " << Expr(hd);
  Kind hk = hdType->getKind();
  if (hk != Kind::FUNCTION_TYPE && hk != Kind::PROGRAM_TYPE)
  {
    // non-function at head
    if (out)
    {
      (*out) << "Non-function " << Expr(hd) << " as head of APPLY" << std::endl;
      (*out) << "Its type is " << Expr(hdType);
    }
    return d_null;
  }
  std::vector<ExprValue*> hdtypes = hdType->d_children;
  std::vector<ExprValue*> ctypes;
  if (hdtypes.size() != children.size())
  {
    // incorrect arity
    if (out)
    {
      (*out) << "Incorrect arity for " << Expr(hd);
      if (hdtypes[hdtypes.size() - 1]->getKind() == Kind::PROOF_TYPE)
      {
        // proof rule can give more information, partioned into args/premises
        size_t npIndex1 = hdtypes.size() - 1;
        while (npIndex1 > 0
               && hdtypes[npIndex1 - 1]->getKind() == Kind::PROOF_TYPE)
        {
          npIndex1--;
        }
        size_t npIndex2 = children.size() - 1;
        while (npIndex2 > 0
               && d_state.lookupType(children[npIndex2 - 1])->getKind()
                      == Kind::PROOF_TYPE)
        {
          npIndex2--;
        }
        (*out) << ", which expects " << npIndex1 << " arguments and "
               << (hdtypes.size() - 1 - npIndex1) << " premises but "
               << npIndex2 << " arguments and "
               << (children.size() - 1 - npIndex2) << " premises were provided";
      }
      else
      {
        (*out) << ", which expects " << (hdtypes.size() - 1)
               << " arguments but " << (children.size() - 1)
               << " were provided";
      }
    }
    return d_null;
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
  // if plugin can evaluate, run the compiled version of the type checker
  if (d_plugin!=nullptr && d_plugin->hasEvaluation(hdType))
  {
    Trace("type_checker") << "RUN type check " << Expr(hdType) << std::endl;
    return d_plugin->getType(hdType, ctypes, out);
  }
  std::set<std::pair<ExprValue*, ExprValue*>> visited;
  Expr hdEval;
  for (size_t i=0, nchild=ctypes.size(); i<nchild; i++)
  {
    Assert(ctypes[i] != nullptr);
    // matching, update context
    ExprValue* hdt = hdtypes[i];
    // if the argument is (Quote t), we match on its argument,
    // which along with how ctypes[i] is the argument itself, has the effect
    // of an implicit upcast.
    hdt = hdt->getKind() == Kind::QUOTE_TYPE ? hdt->d_children[0] : hdt;
    // must evaluate here
    if (hdt->isEvaluatable())
    {
      hdEval = evaluate(hdt, ctx);
      hdt = hdEval.getValue();
    }
    if (!match(hdt, ctypes[i], ctx, visited))
    {
      if (out)
      {
        ExprValue* hdto = hdtypes[i];
        (*out) << "Checking application of " << Expr(hd) << std::endl;
        if (hdtypes[i]->getKind() == Kind::QUOTE_TYPE)
        {
          (*out) << "Unexpected child #" << i << std::endl;
          (*out) << "  Term: " << Expr(children[i + 1]) << std::endl;
          (*out) << "  Expected pattern: ";
          hdto = hdto->d_children[0];
        }
        else
        {
          (*out) << "Unexpected type of child #" << i << std::endl;
          (*out) << "  Term: " << Expr(children[i + 1]) << std::endl;
          (*out) << "  Has type: " << Expr(ctypes[i]) << std::endl;
          (*out) << "  Expected type: ";
        }
        (*out) << Expr(hdt);
        if (hdto != hdt)
        {
          (*out) << ", from " << Expr(hdto);
        }
        (*out) << std::endl;
        (*out) << "  Context " << ctx << std::endl;
      }
      return d_null;
    }
  }
  // evaluate in the matched context
  return evaluate(hdtypes.back(), ctx);
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
    // if we are ground
    if (curr.first->isGround())
    {
      if (curr.first == curr.second)
      {
        // holds trivially
        continue;
      }
      // otherwise fails
      return false;
    }
    // note that if curr.first == curr.second, and both are non-ground,
    // then we still require recursing, which will bind identity substitutions
    // on each of their parameters.
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
        // Special case: if we are an annotated parameter, then matching takes
        // into account its *type*. In particular, the type of the term we are
        // matching is matched against the annotated type. This has the effect
        // that free parameters in the type of parameters are also bound, if the
        // parameter is annotated.
        Kind ck1 = curr.first->getKind();
        if (ck1 == Kind::ANNOT_PARAM)
        {
          stack.emplace_back(curr.first->d_children[0], curr.second);
          // independently check its type
          ExprValue* t = d_state.lookupType(curr.second);
          if (t == nullptr)
          {
            return false;
          }
          stack.emplace_back(curr.first->d_children[1], t);
        }
        else
        {
          return false;
        }
      }
      else
      {
        // recurse on children
        for (size_t i = 0, n = curr.first->getNumChildren(); i < n; ++i)
        {
          stack.emplace_back(curr.first->d_children[i],
                             curr.second->d_children[i]);
        }
      }
    }
  }
  return true;
}

/** Evaluation frame, used in evaluate below. */
class EvFrame
{
 public:
  EvFrame(ExprValue* i, Ctx& ctx, ExprTrie* r) : d_init(i), d_ctx(ctx), d_result(r) {
    if (d_init!=nullptr)
    {
      d_visit.push_back(d_init);
    }
  }
  ~EvFrame(){}
  /** The initial value we are evaluating */
  ExprValue* d_init;
  /** The context it is being evaluated in */
  Ctx d_ctx;
  /** Cache of visited subterms */
  std::unordered_map<ExprValue*, Expr> d_visited;
  /** The subterms to visit */
  std::vector<ExprValue*> d_visit;
  /** An (optional) pointer of a trie of where to store the result */
  ExprTrie * d_result;
};

Expr TypeChecker::evaluate(ExprValue* e, Ctx& ctx)
{
  Assert (e!=nullptr);
  // A trie for all programs/oracles we have evaluated during this call.
  // This is required to ensure that programs that traverse terms recursively
  // preform a dag traversal.
  ExprTrie evalTrie;
  // A set of terms that we are manually incrementing their ref count (via
  // adding them to keepList). This set of terms includes the terms that
  // appear in the above trie.
  std::unordered_set<ExprValue*> keep;
  std::vector<Expr> keepList;
  std::unordered_map<ExprValue*, Expr>::iterator it;
  Ctx::iterator itc;
  // the evaluation stack
  std::vector<EvFrame> estack;
  estack.emplace_back(e, ctx, nullptr);
  Expr evaluated;
  ExprValue* cur;
  Kind ck;
  bool newContext = false;
  bool canEvaluate = true;
  while (!estack.empty())
  {
    EvFrame& evf = estack.back();
    std::unordered_map<ExprValue*, Expr>& visited = evf.d_visited;
    std::vector<ExprValue*>& visit = evf.d_visit;
    Ctx& cctx = evf.d_ctx;
    while (!visit.empty())
    {
      Assert (!newContext && canEvaluate);
      cur = visit.back();
      Trace("type_checker_debug") << "visit " << Expr(cur) << " " << cctx
                                  << ", depth=" << estack.size() << std::endl;
      // the term will stay the same if it is not evaluatable and either it
      // is ground, or the context is empty.
      if (!cur->isEvaluatable() && (cur->isGround() || cctx.empty()))
      {
        //std::cout << "...shortcut " << cur << std::endl;
        visited[cur] = Expr(cur);
        visit.pop_back();
        continue;
      }
      if (cur->getKind()==Kind::PARAM)
      {
        // might be in context
        itc = cctx.find(cur);
        if (itc!=cctx.end())
        {
          visited[cur] = Expr(itc->second);
          visit.pop_back();
          continue;
        }
        visited[cur] = Expr(cur);
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
        if (d_plugin && d_plugin->hasEvaluation(cur))
        {
          Trace("type_checker") << "RUN evaluate " << cur << std::endl;
          Expr retev = d_plugin->evaluate(cur, cctx);
          Assert(!retev.isNull());
          if (!retev.isNull())
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
        visited[cur] = d_null;
        if (ck==Kind::EVAL_IF_THEN_ELSE)
        {
          // if it is malformed, it does not evaluate
          if (children.size()!=3)
          {
            visited[cur] = Expr(cur);
            visit.pop_back();
            continue;
          }
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
        bool cchanged = false;
        for (ExprValue* cp : children)
        {
          it = visited.find(cp);
          if (it != visited.end())
          {
            cchildren.push_back(it->second.getValue());
            if (!cchanged)
            {
              cchanged = (cp!=it->second.getValue());
            }
          }
          else
          {
            // we won't evaluate on this iteration
            cchildren.push_back(nullptr);
          }
        }
        evaluated = d_null;
        switch (ck)
        {
          case Kind::APPLY:
          case Kind::APPLY_OPAQUE:
          {
            Trace("type_checker_debug")
                << "evaluated args " << cchildren << std::endl;
            // if a program and all arguments are ground, run it
            Kind cck = cchildren[0]->getKind();
            if (cck == Kind::PROGRAM_CONST)
            {
              // maybe the evaluation is already cached
              // ensure things in the evalTrie are ref counted
              for (ExprValue* e : cchildren)
              {
                if (keep.insert(e).second)
                {
                  keepList.emplace_back(e);
                }
              }
              ExprTrie* et = evalTrie.get(cchildren);
              if (et->d_data!=nullptr)
              {
                evaluated = Expr(et->d_data);
                Trace("type_checker_debug")
                    << "evaluated via cached evaluation" << std::endl;
              }
              else
              {
                Ctx newCtx;
                // see if we evaluate
                evaluated = evaluateProgramInternal(cchildren, newCtx);
                //std::cout << "Evaluate prog returned " << evaluated << std::endl;
                if (evaluated.isNull() || evaluated.isGround() || newCtx.empty())
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
                  estack.emplace_back(evaluated.getValue(), newCtx, et);
                }
              }
            }
          }
            break;
          case Kind::EVAL_IF_THEN_ELSE:
          {
            Assert (cchildren[0]!=nullptr);
            Assert (children.size()==3);
            // get the evaluation of the condition
            if (cchildren[0]->getKind()==Kind::BOOLEAN)
            {
              const Literal* l = cchildren[0]->asLiteral();
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
                evaluated = Expr(cchildren[index]);
                Trace("type_checker_debug") << "evaluated via ite" << std::endl;
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
              Trace("type_checker_debug")
                  << "evaluated via literal op" << std::endl;
            }
            break;
        }
        if (newContext)
        {
          Trace("type_checker_debug") << "new context" << std::endl;
          break;
        }
        if (canEvaluate)
        {
          if (evaluated.isNull())
          {
            if (cchanged)
            {
              evaluated = Expr(d_state.mkExprInternal(ck, cchildren));
            }
            else
            {
              // children didn't change, just take the original
              evaluated = Expr(cur);
            }
            Trace("type_checker_debug")
                << "evaluated via mkExprInternal" << std::endl;
          }
          visited[cur] = evaluated;
          Trace("type_checker_debug")
              << "visited " << Expr(cur) << " = " << evaluated << std::endl;
          visit.pop_back();
        }
        else
        {
          canEvaluate = true;
          Trace("type_checker_debug") << "cannot evaluate" << std::endl;
        }
      }
      else
      {
        visit.pop_back();
      }
    }
    // if we are done evaluating the current context
    if (!newContext)
    {
      // get the result from the inner evaluation
      ExprValue* init = evf.d_init;
      Assert (evf.d_visited.find(init)!=evf.d_visited.end());
      evaluated = evf.d_visited[init];
      Trace("type_checker") << "EVALUATE " << Expr(init) << ", "
                            << evf.d_ctx << " = " << evaluated << std::endl;
      if (evf.d_result!=nullptr)
      {
        ExprValue * ev = evaluated.getValue();
        if (keep.insert(ev).second)
        {
          keepList.emplace_back(ev);
        }
        evf.d_result->d_data = ev;
      }
      // pop the evaluation context
      estack.pop_back();
      // carry to lower context
      if (!estack.empty())
      {
        EvFrame& evp = estack.back();
        Assert (!evp.d_visit.empty());
        evp.d_visited[evp.d_visit.back()] = evaluated;
        evp.d_visit.pop_back();
      }
    }
    else
    {
      newContext = false;
    }
  }
  return evaluated;
}

Expr TypeChecker::evaluateProgram(
    const std::vector<ExprValue*>& children, Ctx& newCtx)
{
  const Expr& ret = evaluateProgramInternal(children, newCtx);
  if (!ret.isNull())
  {
    return ret;
  }
  // otherwise does not evaluate, return application
  return Expr(d_state.mkExprInternal(Kind::APPLY, children));
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

Expr TypeChecker::evaluateProgramInternal(
    const std::vector<ExprValue*>& children, Ctx& newCtx)
{
  if (!isGround(children))
  {
    // do not evaluate on non-ground
    return d_null;
  }
  // Note we abort here, which changed in Ethos versions >=0.1.2.
  // The motivation is to disallow unintuitive behaviors of Ethos,
  // which includes:
  // - Passing (unapplied) user programs, user oracles or builtin
  // operators, which we do not support in this current version.
  // - Passing stuck terms, where we chose to propagate the failure,
  // e.g. (<program> t) is also stuck if t is stuck.
  size_t nargs = children.size();
  for (size_t j=1; j<nargs; j++)
  {
    if (children[j]->isEvaluatable())
    {
      return d_null;
    }
  }
  ExprValue* hd = children[0];
  Assert(hd->getKind() == Kind::PROGRAM_CONST);
  if (d_plugin && d_plugin->hasEvaluation(hd))
  {
    Trace("type_checker") << "RUN program " << children << std::endl;
    return d_plugin->evaluateProgram(hd, children, newCtx);
  }
  Expr prog = d_state.getProgram(hd);
  if (d_statsEnabled)
  {
    RuleStat* ps = &d_sts.d_pstats[hd];
    ps->d_count++;
  }
  Assert(!prog.isNull());
  if (!prog.isNull())
  {
    Trace("type_checker") << "INTERPRET program " << children << std::endl;
    // otherwise, evaluate
    for (size_t i = 0, nchildren = prog.getNumChildren(); i < nchildren; i++)
    {
      const Expr& c = prog[i];
      newCtx.clear();
      ExprValue* hd = c[0].getValue();
      std::vector<ExprValue*>& hchildren = hd->d_children;
      if (nargs != hchildren.size())
      {
        // TODO: catch this during weak type checking of program bodies
        Warning() << "*** Bad number of arguments provided in function call to "
                  << Expr(hd) << std::endl;
        Warning() << "  Arguments: " << children << std::endl;
        return d_null;
      }
      bool matchSuccess = true;
      for (size_t j = 1; j < nargs; j++)
      {
        if (!match(hchildren[j], children[j], newCtx))
        {
          matchSuccess = false;
          break;
        }
      }
      if (matchSuccess)
      {
        Trace("type_checker")
            << "...matches " << Expr(hd) << ", ctx = " << newCtx << std::endl;
        return c[1];
      }
    }
    Trace("type_checker") << "...failed to match." << std::endl;
  }
  // just return nullptr, which should be interpreted as a failed evaluation
  return d_null;
}

Expr TypeChecker::evaluateLiteralOp(Kind k,
                                    const std::vector<ExprValue*>& args)
{
  Expr ret = evaluateLiteralOpInternal(k, args);
  if (!ret.isNull())
  {
    return ret;
  }
  // otherwise does not evaluate, return application
  return Expr(d_state.mkExprInternal(k, args));
}

/**
 * Get nary children, gets a list of children from op-application e,
 * stores them in children.
 */
ExprValue* getNAryChildren(ExprValue* e,
                           ExprValue* op,
                           ExprValue* checkNil,
                           std::vector<ExprValue*>& children,
                           bool isLeft)
{
  ExprValue* orig = e;
  while (e->getKind()==Kind::APPLY)
  {
    ExprValue* cop = (*e)[0];
    if (cop->getKind() != Kind::APPLY || (*cop)[0] != op)
    {
      break;
    }
    // push back the element
    children.push_back(isLeft ? (*e)[1] : (*cop)[1]);
    // traverse to tail
    e = isLeft ? (*cop)[1] : (*e)[1];
  }
  // must be equal to the nil term, if provided
  if (checkNil!=nullptr && e!=checkNil)
  {
    Warning() << "...expected associative application to end in " << Expr(checkNil) << ", got " << Expr(orig) << std::endl;
    return nullptr;
  }
  return e;
}

/**
 * Return true iff e is an op-list with nil terminator checkNil.
 */
bool isNAryList(ExprValue* e, ExprValue* op, ExprValue* checkNil, bool isLeft)
{
  while (e->getKind() == Kind::APPLY)
  {
    ExprValue* cop = (*e)[0];
    if (cop->getKind() != Kind::APPLY || (*cop)[0] != op)
    {
      break;
    }
    // traverse to tail
    e = isLeft ? (*cop)[1] : (*e)[1];
  }
  // must be equal to the nil term
  return e == checkNil;
}

/**
 * Return the n^th tail of e, where e is assumed to be an f-list
 * of size >= n.
 */
ExprValue* getNAryNthTail(ExprValue* e, bool isLeft, size_t n)
{
  for (size_t i = 0; i < n; i++)
  {
    Assert(e->getKind() == Kind::APPLY && (*e)[0]->getKind() == Kind::APPLY);
    // traverse to tail
    e = isLeft ? (*(*e)[0])[1] : (*e)[1];
  }
  return e;
}

Expr TypeChecker::prependNAryChildren(ExprValue* op,
                                      ExprValue* ret,
                                      const std::vector<ExprValue*>& hargs,
                                      bool isLeft)
{
  // note we take the tail verbatim
  if (isLeft)
  {
    ExprValue* c1;
    for (auto it = hargs.begin(); it != hargs.end(); ++it)
    {
      c1 = d_state.mkExprInternal(Kind::APPLY, {op, ret});
      ret = d_state.mkExprInternal(Kind::APPLY, {c1, *it});
    }
  }
  else
  {
    ExprValue* c1;
    for (auto rit = hargs.rbegin(); rit != hargs.rend(); ++rit)
    {
      c1 = d_state.mkExprInternal(Kind::APPLY, {op, *rit});
      ret = d_state.mkExprInternal(Kind::APPLY, {c1, ret});
    }
  }
  return Expr(ret);
}

Expr TypeChecker::evaluateLiteralOpInternal(
    Kind k, const std::vector<ExprValue*>& args)
{
  Assert (!args.empty());
  Trace("type_checker") << "EVALUATE-LIT " << k << " " << args << std::endl;
  // special cases: ITE may evaluate if non-ground
  switch (k)
  {
    case Kind::EVAL_IF_THEN_ELSE:
    {
      Assert (args.size()==3);
      if (args[0]->getKind()==Kind::BOOLEAN)
      {
        const Literal* l = args[0]->asLiteral();
        // eagerly evaluate even if branches are non-ground
        return Expr(args[l->d_bool ? 1 : 2]);
      }
      // note that we do not simplify based on the branches being equal
      return d_null;
    }
    break;
    case Kind::ANNOT_PARAM:
    {
      // if the first argument is ground, then we know by construction
      // that its type is equal to the second argument. This invariant
      // is ensured by the fact that the context we are in is the result
      // of a context that was extended by matching the second argument
      // to the type of the (instantiated) first argument.
      if (args[0]->isGround())
      {
        // by construction, args[0] should have type args[1], this is
        // an assertion that is not checked in production.
        Expr ret(args[0]);
        Assert(getType(ret).getValue() == args[1]);
        return Expr(ret);
      }
    }
    break;
    case Kind::EVAL_REQUIRES:
    {
      // (eo::requires t s r) ---> r if (eo::is_eq t s) = true
      // Note that this is independent of whether r is ground, and hence is
      // a special case prior to check for all arguments to be ground.
      if (args[0]->isGround() && !args[0]->isEvaluatable()
          && args[1]->isGround() && !args[1]->isEvaluatable()
          && args[0] == args[1])
      {
        return Expr(args[2]);
      }
      if (TraceIsOn("type_checker"))
      {
        if (isGround(args))
        {
          Trace("type_checker") << "REQUIRES: failed " << Expr(args[0])
                                << " == " << Expr(args[1]) << std::endl;
        }
      }
      return d_null;
    }
    break;
    default: break;
  }
  // further evaluation only if non-ground
  if (!isGround(args))
  {
    Trace("type_checker") << "...does not evaluate (non-ground)" << std::endl;
    return d_null;
  }
  switch (k)
  {
    case Kind::EVAL_IS_OK:
    {
      Assert(args.size() == 1);
      // returns false iff the argument is stuck, only evaluated if the argument
      // is ground.
      return d_state.mkBool(!args[0]->isEvaluatable());
    }
    break;
    case Kind::EVAL_IS_EQ:
    {
      Assert(args.size() == 2);
      // Note that (eo::is_eq t s) is equivalent to
      // (eo::ite (eo::and (eo::is_ok t) (eo::is_ok s)) (eo::eq s t) false)
      // In other words, eo::is_eq if true if both arguments are syntactically
      // equal and not stuck, false otherwise.
      // Since eo::and does not short circuit, this means that the condition of
      // the ITE is only evaluated when t and s are ground, hence eo::is_eq
      // only evaluates when its arguments are ground, and so it is handled
      // here.
      return d_state.mkBool(!args[0]->isEvaluatable()
                            && !args[1]->isEvaluatable() && args[0] == args[1]);
    }
    break;
    case Kind::EVAL_EQ:
    {
      // syntactic equality, only evaluated if the terms are values
      if (!args[0]->isEvaluatable() && !args[1]->isEvaluatable())
      {
        return d_state.mkBool(args[0] == args[1]);
      }
      // does not evaluate otherwise
      return d_null;
    }
    break;
    case Kind::EVAL_HASH:
    {
      Assert(args.size() == 1);
      if (args[0]->isEvaluatable())
      {
        return d_null;
      }
      size_t h = d_state.getHash(args[0]);
      Literal lh(Integer(static_cast<unsigned int>(h)));
      return Expr(d_state.mkLiteralInternal(lh));
    }
    break;
    case Kind::EVAL_COMPARE:
    {
      if (args[0]->isEvaluatable() || args[1]->isEvaluatable())
      {
        return d_null;
      }
      size_t h1 = d_state.getHash(args[0]);
      size_t h2 = d_state.getHash(args[1]);
      Literal lb(h1 > h2);
      return Expr(d_state.mkLiteralInternal(lb));
    }
    break;
    case Kind::EVAL_IS_Z:
    case Kind::EVAL_IS_Q:
    case Kind::EVAL_IS_BIN:
    case Kind::EVAL_IS_STR:
    case Kind::EVAL_IS_BOOL:
    case Kind::EVAL_IS_VAR:
    {
      Assert(args.size() == 1);
      Kind kk;
      switch (k)
      {
      case Kind::EVAL_IS_Z:kk = Kind::NUMERAL;break;
      case Kind::EVAL_IS_Q:kk = Kind::RATIONAL;break;
      case Kind::EVAL_IS_BIN:kk = Kind::BINARY;break;
      case Kind::EVAL_IS_STR:kk = Kind::STRING;break;
      case Kind::EVAL_IS_BOOL:kk = Kind::BOOLEAN;break;
      case Kind::EVAL_IS_VAR:kk = Kind::VARIABLE;break;
      default: Assert(false); break;
      }
      Literal lb(args[0]->getKind()==kk);
      return Expr(d_state.mkLiteralInternal(lb));
    }
    break;
    case Kind::EVAL_TYPE_OF:
    {
      if (!args[0]->isEvaluatable())
      {
        // get the type if ground
        Expr e(args[0]);
        Expr et = getType(e);
        if (et.isGround())
        {
          // don't permit ground evaluatable types
          Assert(!et.isEvaluatable());
          return et;
        }
      }
    }
    break;
    case Kind::EVAL_NAME_OF:
    {
      Kind k = args[0]->getKind();
      if (k == Kind::CONST || k == Kind::VARIABLE)
      {
        Literal sym(String(Expr(args[0]).getSymbol()));
        return Expr(d_state.mkLiteralInternal(sym));
      }
    }
    break;
    case Kind::EVAL_VAR:
    {
      // if arguments are ground and the first argument is a string
      if (args[0]->getKind() == Kind::STRING && !args[1]->isEvaluatable())
      {
        Expr type(args[1]);
        Expr tt = getType(type);
        if (!tt.isNull() && tt.getKind()==Kind::TYPE)
        {
          const Literal* l = args[0]->asLiteral();
          return d_state.getBoundVar(l->d_str.toString(), type);
        }
      }
    }
    break;
    case Kind::EVAL_DT_SELECTORS:
    {
      // it may be an ambiguous constructor with an annotation, in which
      // case we extract the underlying symbol
      Expr sym(args[0]);
      sym = sym.getKind() == Kind::APPLY_OPAQUE ? sym[0] : sym;
      AppInfo* ac = d_state.getAppInfo(sym.getValue());
      if (ac != nullptr)
      {
        Assert(args[0]->isGround());
        Attr a = ac->d_attrCons;
        if (a == Attr::DATATYPE_CONSTRUCTOR
            || a == Attr::AMB_DATATYPE_CONSTRUCTOR)
        {
          return ac->d_attrConsTerm;
        }
      }
      return d_null;
    }
    break;
    case Kind::EVAL_DT_CONSTRUCTORS:
    {
      Expr sym(args[0]);
      // It might be a parametric datatype? We check if it is an apply and
      // that it is fully applied (i.e. its type is Type).
      bool isParam = false;
      if (sym.getKind() == Kind::APPLY && getType(sym) == d_state.mkType())
      {
        isParam = true;
        do
        {
          sym = sym[0];
        } while (sym.getKind() == Kind::APPLY);
      }
      AppInfo* ac = d_state.getAppInfo(sym.getValue());
      if (ac != nullptr && ac->d_attrCons == Attr::DATATYPE)
      {
        // if parametric, add opaque argument annotations to constructors
        // that are marked as AMB_DATATYPE_CONSTRUCTOR.
        if (isParam)
        {
          std::vector<ExprValue*> cargs;
          Expr cop = d_state.mkListCons();
          getNAryChildren(ac->d_attrConsTerm.getValue(),
                          cop.getValue(),
                          nullptr,
                          cargs,
                          false);
          std::vector<Expr> cargsp;
          for (ExprValue* c : cargs)
          {
            Expr ce(c);
            if (d_state.getConstructorKind(c) == Attr::AMB_DATATYPE_CONSTRUCTOR)
            {
              Expr dt(args[0]);
              ce = d_state.mkExpr(Kind::APPLY_OPAQUE, {ce, dt});
            }
            cargsp.push_back(ce);
          }
          return d_state.mkList(cargsp);
        }
        return ac->d_attrConsTerm;
      }
      return d_null;
    }
    break;
    default:
      break;
  }
  // convert argument expressions to literals
  std::vector<const Literal*> lits;
  bool allValues = true;
  for (ExprValue* e : args)
  {
    // symbols are stored as literals but do not evaluate
    if (!isLiteral(e->getKind()))
    {
      Trace("type_checker") << "...does not value-evaluate (argument)" << std::endl;
      // failed to convert an argument
      allValues = false;
      break;
    }
    lits.push_back(e->asLiteral());
  }
  // if all values, run the literal evaluator
  if (allValues)
  {
    if (!checkArity(k, args.size()))
    {
      Warning() << "Wrong number of arguments when applying literal op " << k
                << ", " << args.size() << " arguments (" << args << ")" << std::endl;
      // does not evaluate if arity is wrong
      return d_null;
    }
    // evaluate
    Literal eval = Literal::evaluate(k, lits);
    if (eval.getKind()==Kind::NONE)
    {
      Trace("type_checker") << "...does not value-evaluate (return)" << std::endl;
      // failed to evaluate
      return d_null;
    }
    // convert back to an expression
    Expr lit = Expr(d_state.mkLiteralInternal(eval));
    Trace("type_checker") << "...value-evaluates to " << lit << std::endl;
    return lit;
  }
  if (!isListLiteralOp(k))
  {
    return d_null;
  }
  // otherwise, maybe a list operation
  ExprValue* op = args[0];
  // strip off parameterized to look up AppInfo
  op = op->getKind()==Kind::PARAMETERIZED ? (*op)[1] : op;
  AppInfo* ac = d_state.getAppInfo(op);
  if (ac==nullptr)
  {
    Trace("type_checker") << "...not list op, return null" << std::endl;
    // not an associative operator
    return d_null;
  }
  Attr ck = ac->d_attrCons;
  if (ck!=Attr::RIGHT_ASSOC_NIL && ck!=Attr::LEFT_ASSOC_NIL)
  {
    // not an associative operator
    return d_null;
  }
  bool isLeft = (ck==Attr::LEFT_ASSOC_NIL);
  Trace("type_checker_debug") << "EVALUATE-LIT (list) " << k << " " << isLeft << " " << args << std::endl;
  // infer the nil expression, which depends on the type of args[1]
  std::vector<Expr> eargs;
  eargs.emplace_back(args[0]);
  Expr nilExpr;
  if (k==Kind::EVAL_NIL)
  {
    // Special case: to handle (eo::nil x T), we construct
    // a dummy term of type T to be consistent with other
    // lookups for nil terminators.
    Expr tmpType(args[1]);
    Expr tmp = d_state.mkSymbol(Kind::CONST, "tmp", tmpType);
    eargs.emplace_back(tmp);
    return computeConstructorTermInternal(ac, eargs);
  }
  else if (args.size()>1)
  {
    eargs.emplace_back(args[1]);
    nilExpr = computeConstructorTermInternal(ac, eargs);
  }
  if (nilExpr.isNull())
  {
    Trace("type_checker") << "...failed to get nil" << std::endl;
    return d_null;
  }
  ExprValue * nil = nilExpr.getValue();
  ExprValue* ret;
  std::vector<ExprValue*> hargs;
  switch (k)
  {
    case Kind::EVAL_CONS:
    case Kind::EVAL_LIST_CONCAT:
    {
      bool isConcat = (k == Kind::EVAL_LIST_CONCAT);
      size_t tailIndex = (isLeft ? 1 : 2);
      size_t headIndex = (isLeft ? 2 : 1);
      ret = args[isConcat ? tailIndex : 2];
      if (!isNAryList(ret, op, nil, isLeft))
      {
        Trace("type_checker") << "...tail not in list form, nil is " << nilExpr << std::endl;
        // tail is not in list form
        return d_null;
      }
      if (k==Kind::EVAL_CONS)
      {
        hargs.push_back(args[1]);
      }
      else
      {
        // extract all children of the head
        ExprValue* a = getNAryChildren(args[headIndex], op, nil, hargs, isLeft);
        if (a==nullptr)
        {
          Trace("type_checker") << "...head not in list form" << std::endl;
          // head is not in list form
          return d_null;
        }
        // if second arg is nil, no need to reconstruct the first arg
        if (ret == nil)
        {
          return Expr(args[headIndex]);
        }
      }
      return prependNAryChildren(op, ret, hargs, isLeft);
    }
      break;
    case Kind::EVAL_LIST_LENGTH:
    {
      ExprValue* a = getNAryChildren(args[1], op, nil, hargs, isLeft);
      if (a==nullptr)
      {
        Trace("type_checker") << "...head not in list form" << std::endl;
        return d_null;
      }
      Literal lret = Literal(Integer(hargs.size()));
      return Expr(d_state.mkLiteralInternal(lret));
    }
      break;
    case Kind::EVAL_LIST_NTH:
    {
      // (eo::extract <op> <term> <n>) returns the n^th child of <op>-application <term>
      if (args[2]->getKind()!=Kind::NUMERAL)
      {
        return d_null;
      }
      const Integer& index = args[2]->asLiteral()->d_int;
      if (!index.fitsUnsignedInt())
      {
        return d_null;
      }
      size_t i = index.toUnsignedInt();
      // extract all children, to ensure a list
      ExprValue* a = getNAryChildren(args[1], op, nil, hargs, isLeft);
      if (a == nullptr || i >= hargs.size())
      {
        return d_null;
      }
      return Expr(hargs[i]);
    }
      break;
    case Kind::EVAL_LIST_FIND:
    {
      ExprValue* a = getNAryChildren(args[1], op, nil, hargs, isLeft);
      if (a==nullptr)
      {
        Trace("type_checker") << "...head not in list form" << std::endl;
        return d_null;
      }
      std::vector<ExprValue*>::iterator it = std::find(hargs.begin(), hargs.end(), args[2]);
      if (it==hargs.end())
      {
        if (d_negOne.isNull())
        {
          Literal lno(Integer("-1"));
          d_negOne = Expr(d_state.mkLiteralInternal(lno));
        }
        return d_negOne;
      }
      size_t iret = std::distance(hargs.begin(), it);
      Literal lret = Literal(Integer(iret));
      return Expr(d_state.mkLiteralInternal(lret));
    }
    break;
    case Kind::EVAL_LIST_ERASE:
    case Kind::EVAL_LIST_ERASE_ALL:
      return evaluateListEraseInternal(k, op, nil, isLeft, args);
    case Kind::EVAL_LIST_REV:
      return evaluateListRevInternal(op, nil, isLeft, args);
    case Kind::EVAL_LIST_SETOF:
      return evaluateListSetOfInternal(op, nil, isLeft, args);
    case Kind::EVAL_LIST_MINCLUDE:
    case Kind::EVAL_LIST_MEQ:
      return evaluateListMPredInternal(k, op, nil, isLeft, args);
    case Kind::EVAL_LIST_DIFF:
    case Kind::EVAL_LIST_INTER:
      return evaluateListDiffInterInternal(k, op, nil, isLeft, args);
    default:
      break;
  }
  return d_null;
}

Expr TypeChecker::evaluateListRevInternal(ExprValue* op,
                                          ExprValue* nil,
                                          bool isLeft,
                                          const std::vector<ExprValue*>& args)
{
  std::vector<ExprValue*> hargs;
  if (getNAryChildren(args[1], op, nil, hargs, isLeft) == nullptr)
  {
    Trace("type_checker") << "...head not in list form" << std::endl;
    return d_null;
  }
  std::reverse(hargs.begin(), hargs.end());
  return prependNAryChildren(op, nil, hargs, isLeft);
}

Expr TypeChecker::evaluateListEraseInternal(Kind k,
                                            ExprValue* op,
                                            ExprValue* nil,
                                            bool isLeft,
                                            const std::vector<ExprValue*>& args)
{
  std::vector<ExprValue*> hargs;
  if (getNAryChildren(args[1], op, nil, hargs, isLeft) == nullptr)
  {
    return d_null;
  }
  std::vector<ExprValue*> result;
  bool isAll = (k == Kind::EVAL_LIST_ERASE_ALL);
  size_t changeIndex = 0;
  size_t changeSize = 0;
  for (size_t i = 0, nargs = hargs.size(); i < nargs; i++)
  {
    if (hargs[i] == args[2])
    {
      changeIndex = i + 1;
      if (!isAll)
      {
        break;
      }
      changeSize = result.size();
      continue;
    }
    result.emplace_back(hargs[i]);
  }
  if (changeIndex == 0)
  {
    return Expr(args[1]);
  }
  // We resize to the size of the vector at the place it was last modified,
  // and take the changeIndex^th tail of args[1]. This is an important
  // optimization to avoid reconstructing the remainder of the list past
  // the point it was changed.
  if (isAll)
  {
    result.resize(changeSize);
  }
  ExprValue* ret = getNAryNthTail(args[1], isLeft, changeIndex);
  return prependNAryChildren(op, ret, result, isLeft);
}

Expr TypeChecker::evaluateListSetOfInternal(ExprValue* op,
                                            ExprValue* nil,
                                            bool isLeft,
                                            const std::vector<ExprValue*>& args)
{
  std::vector<ExprValue*> hargs;
  if (getNAryChildren(args[1], op, nil, hargs, isLeft) == nullptr)
  {
    return d_null;
  }
  std::unordered_set<ExprValue*> seen;
  std::vector<ExprValue*> result;
  size_t changeIndex = 0;
  size_t changeSize = 0;
  for (size_t i = 0, nargs = hargs.size(); i < nargs; i++)
  {
    ExprValue* elem = hargs[i];
    if (seen.insert(elem).second)
    {
      result.emplace_back(elem);
    }
    else
    {
      changeIndex = i + 1;
      changeSize = result.size();
    }
  }
  if (changeIndex == 0)
  {
    return Expr(args[1]);
  }
  // Similar to erase, for performance, we resize to the size of the vector at
  // the place it was last modified, and take the changeIndex^th tail of
  // args[1].
  result.resize(changeSize);
  ExprValue* ret = getNAryNthTail(args[1], isLeft, changeIndex);
  return prependNAryChildren(op, ret, result, isLeft);
}

Expr TypeChecker::evaluateListMPredInternal(Kind k,
                                            ExprValue* op,
                                            ExprValue* nil,
                                            bool isLeft,
                                            const std::vector<ExprValue*>& args)
{
  std::vector<ExprValue*> hargs, hargs2;
  if (getNAryChildren(args[1], op, nil, hargs, isLeft) == nullptr
      || getNAryChildren(args[2], op, nil, hargs2, isLeft) == nullptr)
  {
    return d_null;
  }
  // optimization: reflexive true
  if (args[1] == args[2])
  {
    return d_state.mkTrue();
  }
  std::unordered_map<const ExprValue*, uint32_t> count1, count2;
  for (const ExprValue* elem : hargs)
  {
    ++count1[elem];
  }
  for (const ExprValue* elem : hargs2)
  {
    ++count2[elem];
  }
  bool isEq = (k == Kind::EVAL_LIST_MEQ);
  // if equal, must be same size, this further ensures we only need to check
  // equal elements in one direction.
  if (isEq && count1.size() != count2.size())
  {
    return d_state.mkFalse();
  }
  for (const std::pair<const ExprValue* const, uint32_t>& entry : count1)
  {
    if (isEq ? count2[entry.first] != entry.second
             : count2[entry.first] < entry.second)
    {
      return d_state.mkFalse();
    }
  }
  return d_state.mkTrue();
}

Expr TypeChecker::evaluateListDiffInterInternal(
    Kind k,
    ExprValue* op,
    ExprValue* nil,
    bool isLeft,
    const std::vector<ExprValue*>& args)
{
  std::vector<ExprValue*> hargs, hargs2;
  if (getNAryChildren(args[1], op, nil, hargs, isLeft) == nullptr
      || getNAryChildren(args[2], op, nil, hargs2, isLeft) == nullptr)
  {
    return d_null;
  }
  bool isDiff = (k == Kind::EVAL_LIST_DIFF);
  // optimization: reflexive is nil or self
  if (args[1] == args[2])
  {
    return isDiff ? Expr(nil) : Expr(args[1]);
  }
  std::unordered_map<const ExprValue*, uint32_t> count2;
  for (const ExprValue* elem : hargs2)
  {
    ++count2[elem];
  }
  size_t changeIndex = 0;
  size_t changeSize = 0;
  std::vector<ExprValue*> result;
  std::unordered_map<const ExprValue*, uint32_t>::iterator itc;
  for (size_t i = 0, nargs = hargs.size(); i < nargs; i++)
  {
    itc = count2.find(hargs[i]);
    bool found = (itc != count2.end());
    if (found)
    {
      itc->second--;
      if (itc->second == 0)
      {
        count2.erase(hargs[i]);
      }
    }
    if (found == isDiff)
    {
      changeIndex = i + 1;
      changeSize = result.size();
      continue;
    }
    result.emplace_back(hargs[i]);
  }
  if (changeIndex == 0)
  {
    return Expr(args[1]);
  }
  // We resize to the size of the vector at the place it was last modified,
  // and take the changeIndex^th tail of args[1]. This is an important
  // optimization to avoid reconstructing the remainder of the list past
  // the point it was changed.
  result.resize(changeSize);
  ExprValue* ret = getNAryNthTail(args[1], isLeft, changeIndex);
  return prependNAryChildren(op, ret, result, isLeft);
}

Expr TypeChecker::getLiteralOpType(Kind k,
                                   std::vector<ExprValue*>& children,
                                   std::vector<ExprValue*>& childTypes,
                                   std::ostream* out)
{
  if (!checkArity(k, childTypes.size(), out))
  {
    return d_null;
  }
  // NOTE: applications of most of these operators should only be in patterns,
  // where type checking is not strict.
  switch (k)
  {
    case Kind::EVAL_TYPE_OF:
      return d_state.mkType();
    case Kind::EVAL_VAR:
    case Kind::EVAL_NIL:
      // its type is the second argument
      return Expr(children[1]);
    case Kind::EVAL_ADD:
    case Kind::EVAL_MUL:
      // NOTE: mixed arith
      return Expr(childTypes[0]);
    case Kind::EVAL_NEG:
    case Kind::EVAL_AND:
    case Kind::EVAL_OR:
    case Kind::EVAL_XOR:
    case Kind::EVAL_NOT:
      return Expr(childTypes[0]);
    case Kind::EVAL_IF_THEN_ELSE:
    case Kind::EVAL_CONS:
      return Expr(childTypes[1]);
    case Kind::EVAL_REQUIRES:
      return Expr(childTypes[2]);
    case Kind::EVAL_LIST_CONCAT:
    case Kind::EVAL_LIST_NTH:
    case Kind::EVAL_LIST_ERASE:
    case Kind::EVAL_LIST_ERASE_ALL:
    case Kind::EVAL_LIST_REV:
    case Kind::EVAL_LIST_SETOF:
    case Kind::EVAL_LIST_DIFF:
    case Kind::EVAL_LIST_INTER: return Expr(childTypes[1]);
    case Kind::EVAL_CONCAT:
    case Kind::EVAL_EXTRACT:
      // type is the first child
      return Expr(childTypes[0]);
    case Kind::EVAL_IS_OK:
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_EQ:
    case Kind::EVAL_IS_NEG:
    case Kind::EVAL_COMPARE:
    case Kind::EVAL_IS_Z:
    case Kind::EVAL_IS_Q:
    case Kind::EVAL_IS_BIN:
    case Kind::EVAL_IS_STR:
    case Kind::EVAL_IS_BOOL:
    case Kind::EVAL_IS_VAR:
    case Kind::EVAL_GT:
    case Kind::EVAL_LIST_MINCLUDE:
    case Kind::EVAL_LIST_MEQ: return d_state.mkBoolType();
    case Kind::EVAL_HASH:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_INT_MOD:
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_LENGTH:
    case Kind::EVAL_FIND:
    case Kind::EVAL_LIST_LENGTH:
    case Kind::EVAL_LIST_FIND:
      return getOrSetLiteralTypeRule(Kind::NUMERAL);
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_TO_RAT:
      return getOrSetLiteralTypeRule(Kind::RATIONAL);
    case Kind::EVAL_NAME_OF:
    case Kind::EVAL_TO_STRING:
      return getOrSetLiteralTypeRule(Kind::STRING);
    case Kind::EVAL_TO_BIN:
      return getOrSetLiteralTypeRule(Kind::BINARY);
    case Kind::EVAL_DT_CONSTRUCTORS:
    case Kind::EVAL_DT_SELECTORS: return d_state.mkListType();
    default:break;
  }
  if (out)
  {
    (*out) << "Unknown type for literal operator " << k;
  }
  return d_null;
}

Expr TypeChecker::computeConstructorTermInternal(
    AppInfo* ai, const std::vector<Expr>& children)
{
  if (ai==nullptr)
  {
    return d_null;
  }
  // lookup the base operator if necessary
  Expr ct = ai->d_attrConsTerm;
  if (ct.isNull() || ct.getKind()!=Kind::PARAMETERIZED)
  {
    // if not parameterized, just return self
    return ct;
  }
  const Expr& hd = children[0];
  Trace("type_checker") << "Determine constructor term for " << hd << std::endl;
  // if explicit parameters, then evaluate the constructor term
  if (children.size() == 1)
  {
    // if not in an application, we fail
    Warning() << "Failed to determine parameters for " << hd << std::endl;
    return d_null;
  }
  // otherwise, we must infer the parameters
  Trace("type_checker") << "Infer params for " << hd << " @ " << children[1]
                        << std::endl;
  if (!isNAryAttr(ai->d_attrCons))
  {
    Warning() << "Unknown category for parameterized operator " << hd
              << std::endl;
    return d_null;
  }
  std::vector<ExprValue*> app;
  app.push_back(hd.getValue());
  app.push_back(children[1].getValue());
  // ensure children are type checked
  for (ExprValue* e : app)
  {
    Expr expr(e);
    getType(expr);
    ExprValue* t = d_state.lookupType(e);
    if (t == nullptr)
    {
      // only warn if ground
      if (expr.isGround())
      {
        Warning() << "Type inference failed for " << hd << " applied to "
                  << children[1] << ", failed to type check " << expr
                  << std::endl;
      }
      return d_null;
    }
    Trace("type_checker_debug")
        << "Type for " << expr << " is " << Expr(t) << std::endl;
  }
  Ctx tctx;
  getTypeAppInternal(app, tctx);
  Trace("type_checker_debug") << "Context was " << tctx << std::endl;
  for (size_t i = 0, nparams = ct[0].getNumChildren(); i < nparams; i++)
  {
    ExprValue* cv = tctx[ct[0][i].getValue()];
    if (cv==nullptr)
    {
      Warning() << "Failed to find context for " << ct[0][i]
                << " when applying " << hd << " @ " << children[1] << std::endl;
      return d_null;
    }
    if (!cv->isGround())
    {
      // If the parameter is non-ground, we also wait to construct;
      // if the nil terminator is used, it will be replaced by a
      // placeholder involving eo::nil.
      return d_null;
    }
  }
  Trace("type_checker") << "Context for constructor term: " << tctx
                        << std::endl;
  return evaluate(ct[1].getValue(), tctx);
}

}  // namespace ethos
