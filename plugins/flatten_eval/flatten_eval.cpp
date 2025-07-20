/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "flatten_eval.h"

namespace ethos {

ProgramOutCtx::ProgramOutCtx(State& s, const std::string& progPrefix)
    : d_state(s), d_progPrefix(progPrefix), d_varCount(0), d_progCount(0)
{
}

Expr ProgramOutCtx::getTypeInternal(const Expr& e)
{
  Expr etmp = e;
  Expr te = d_state.getTypeChecker().getType(etmp);
  // if type is null, then we can introduce a type parameter
  // this gives a warning
  if (te.isNull())
  {
    std::cout << "WARNING: unknown type for " << e << std::endl;
    te = d_state.mkSymbol(Kind::PARAM, "tmp", d_state.mkType());
  }
  return te;
}
void ProgramOutCtx::pushArg(const Expr& a)
{
  Expr taa = getTypeInternal(a);
  pushArgTyped(a, taa);
}

void ProgramOutCtx::pushArgTyped(const Expr& a, const Expr& at)
{
  d_args.push_back(a);
  d_argTypes.push_back(at);
}

void ProgramOutCtx::popArg()
{
  Assert(!d_args.empty());
  d_args.pop_back();
  d_argTypes.pop_back();
}

Expr ProgramOutCtx::allocateProgram(const std::vector<Expr>& nvars,
                                    const std::vector<Expr>& nargs,
                                    const Expr& ret)
{
  Assert(nvars.size() == nargs.size());
  size_t numVars = nvars.size();
  for (size_t i = 0; i < numVars; i++)
  {
    pushArg(nvars[i]);
  }
  Expr retType = getTypeInternal(ret);
  Expr prog = allocateProgramInternal(retType);

  // the case
  Expr progCase = mkCurrentProgramPat(prog);
  Expr progPair = d_state.mkPair(progCase, ret);
  Expr progDef = d_state.mkExpr(Kind::PROGRAM, {progPair});
  d_progAlloc.emplace_back(prog, progDef);
  for (size_t i = 0; i < numVars; i++)
  {
    popArg();
  }
  std::vector<Expr> pappChildren;
  pappChildren.push_back(prog);
  pappChildren.insert(pappChildren.end(), d_args.begin(), d_args.end());
  for (size_t i = 0; i < numVars; i++)
  {
    pappChildren.push_back(ensureFinalArg(nargs[i]));
  }
  Expr progApp = d_state.mkExprSimple(Kind::APPLY, pappChildren);
  return progApp;
}

Expr ProgramOutCtx::mkCurrentProgramPat(const Expr& prog)
{
  std::vector<Expr> pcChildren;
  pcChildren.push_back(prog);
  pcChildren.insert(pcChildren.end(), d_args.begin(), d_args.end());
  return d_state.mkExprSimple(Kind::APPLY, pcChildren);
}

Expr ProgramOutCtx::allocateProgramInternal(const Expr& retType)
{
  Assert(!retType.isNull());
  Expr progType = d_state.mkProgramType(d_argTypes, retType);
  d_progCount++;
  std::stringstream ss;
  ss << d_progPrefix << "." << d_progCount;
  return d_state.mkSymbol(Kind::PROGRAM_CONST, ss.str(), progType);
}

Expr ProgramOutCtx::allocateVariable(const Expr& retType)
{
  Assert(!retType.isNull());
  d_varCount++;
  std::stringstream ss;
  ss << "$eo_" << d_varCount;
  return d_state.mkSymbol(Kind::PARAM, ss.str(), retType);
}

Expr ProgramOutCtx::ensureFinalArg(const Expr& e)
{
  Kind k = e.getKind();
  if (k == Kind::EVAL_IF_THEN_ELSE)
  {
    Expr et = getTypeInternal(e);
    Expr btrue = d_state.mkTrue();
    Expr prog;
    std::vector<Expr> pcs;
    for (size_t i = 0; i < 2; i++)
    {
      Expr bvalue = d_state.mkBool(i == 0);
      Expr progRet = i == 0 ? e[1] : e[2];
      pushArg(bvalue);
      if (i == 0)
      {
        prog = allocateProgramInternal(et);
      }
      Expr progCase = mkCurrentProgramPat(prog);
      Expr progPair = d_state.mkPair(progCase, progRet);
      pcs.push_back(progPair);
      popArg();
    }
    Expr progDef = d_state.mkExpr(Kind::PROGRAM, pcs);
    d_progAlloc.emplace_back(prog, progDef);
    std::vector<Expr> pappChildren;
    pappChildren.push_back(prog);
    pappChildren.insert(pappChildren.end(), d_args.begin(), d_args.end());
    pappChildren.push_back(e[0]);
    return d_state.mkExprSimple(Kind::APPLY, pappChildren);
  }
  else if (k == Kind::EVAL_REQUIRES)
  {
    Expr et = getTypeInternal(e);
    Expr prog = allocateProgramInternal(et);
    Expr var = allocateVariable(et);
    // args 0 and 1 must be equal, or else we are not evaluated
    pushArg(var);
    pushArg(var);
    Expr progCase = mkCurrentProgramPat(prog);
    Expr progPair = d_state.mkPair(progCase, e[2]);
    Expr progDef = d_state.mkExpr(Kind::PROGRAM, {progPair});
    d_progAlloc.emplace_back(prog, progDef);
    popArg();
    popArg();
    std::vector<Expr> pappChildren;
    pappChildren.push_back(prog);
    pappChildren.insert(pappChildren.end(), d_args.begin(), d_args.end());
    pappChildren.push_back(e[0]);
    pappChildren.push_back(e[1]);
    return d_state.mkExprSimple(Kind::APPLY, pappChildren);
  }
  return e;
}

FlattenEval::FlattenEval(State& s) : StdPlugin(s) {}
FlattenEval::~FlattenEval() {}

Expr FlattenEval::flattenEval(State& s, ProgramOutCtx& ctx, const Expr& t)
{
  // get the free variables, which will be the arguments
  // to potential programs
  std::vector<Expr> vars = Expr::getVariables(t);
  if (vars.empty())
  {
    // if ground, there is nothing to do
    Assert(!t.isEvaluatable()) << "Static stuck evaluation";
    return t;
  }
  Expr ret = t;
  for (const Expr& v : vars)
  {
    ctx.pushArg(v);
  }
  std::vector<Expr> nevals;
  // local context??
  std::map<Expr, Expr>& visited = ctx.d_visited;
  visited.clear();
  Expr tp = mkPurifyEvaluation(s, t, ctx, nevals);
  if (tp != t)
  {
    // get the variables we use to purify nevals
    std::vector<Expr> nvars;
    for (size_t i = 0, nnewEval = nevals.size(); i < nnewEval; i++)
    {
      Expr ceval = nevals[i];
      Expr cvar = visited[ceval];
      Assert(!cvar.isNull() && cvar.getKind() == Kind::PARAM);
      nvars.push_back(cvar);
    }
    // Allocate a program which has new variables that were introduced
    // to construct tp. We call this program with the terms we purified.
    // The actual terms in nevals may be processed further to eliminate
    // ite and requires.
    ret = ctx.allocateProgram(nvars, nevals, tp);
  }
  for (size_t i = 0, npush = vars.size(); i < npush; i++)
  {
    ctx.popArg();
  }
  return ret;
}

bool FlattenEval::isFinal(const Expr& e)
{
  Kind ek = e.getKind();
  if (ek == Kind::EVAL_IF_THEN_ELSE || ek == Kind::EVAL_REQUIRES)
  {
    return false;
  }
  return isPure(e);
}

size_t FlattenEval::deferIndex(const Expr& e)
{
  Kind k = e.getKind();
  return (k == Kind::EVAL_IF_THEN_ELSE
              ? 1
              : (k == Kind::EVAL_REQUIRES ? 2 : e.getNumChildren()));
}

bool FlattenEval::isPure(const Expr& e)
{
  if (!e.isEvaluatable())
  {
    // terms with no evaluation in them are pure
    return true;
  }
  Kind k = e.getKind();
  // if we have evaluation, and aren't a top-level application of evaluation,
  // we are not pure (likely we are an APPLY with nested evaluation).
  if ((k != Kind::APPLY || e[0].getKind() != Kind::PROGRAM_CONST)
      && !isLiteralOp(k))
  {
    return false;
  }
  // we are not pure if one of our relevant children is not pure.
  size_t istart = (k == Kind::APPLY ? 1 : 0);
  size_t iend = deferIndex(e);
  for (size_t i = istart; i < iend; i++)
  {
    if (e[i].isEvaluatable())
    {
      // TODO: cache
      // requires or ite as strict children are not allowed
      if (!isFinal(e[i]))
      {
        return false;
      }
      // if the argument is pure, we are ok, for instance
      // (f (g x) y) is ok where f and g are programs.
    }
  }
  return true;
}

Expr FlattenEval::mkPurifyEvaluation(State& s,
                                     const Expr& e,
                                     ProgramOutCtx& ctx,
                                     std::vector<Expr>& newEvals)
{
  if (isFinal(e))
  {
    // if it is already final, we are done, otherwise we will
    // preprocess it.
    return e;
  }
  Expr nullExpr;
  std::map<Expr, Expr>& visited = ctx.d_visited;
  std::map<Expr, Expr>::iterator it;
  std::vector<Expr> visit;
  Expr cur;
  visit.push_back(e);
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    Kind k = cur.getKind();
    if (it == visited.end())
    {
      // if not evaluatable, self
      if (!cur.isEvaluatable())
      {
        visited[cur] = cur;
        visit.pop_back();
        continue;
      }
      else if (isPure(cur))
      {
        newEvals.emplace_back(cur);
        Expr curt = s.getTypeChecker().getType(cur);
        if (curt.isNull())
        {
          std::cout << "WARNING: Failed to type check " << cur << std::endl;
          curt = s.mkAny();
        }
        Expr v = ctx.allocateVariable(curt);
        visited[cur] = v;
        visit.pop_back();
        continue;
      }
      visited[cur] = nullExpr;
      size_t iend = deferIndex(cur);
      for (size_t i = 0; i < iend; i++)
      {
        visit.push_back(cur[i]);
      }
      continue;
    }
    visit.pop_back();
    if (it->second.isNull())
    {
      Expr ret = cur;
      bool childChanged = false;
      std::vector<Expr> children;
      for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
      {
        Expr cn = cur[i];
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = Expr(s.mkExprSimple(k, children));
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(e) != visited.end());
  Assert(!visited.find(e)->second.isNull());
  return visited[e];
}

std::vector<std::pair<Expr, Expr>> FlattenEval::flattenProgram(
    State& s,
    const Expr& prog,
    const Expr& progDef,
    std::map<Expr, Expr>& typeMap)
{
  std::vector<std::pair<Expr, Expr>> ret;
  std::vector<std::pair<Expr, Expr>> toVisit;
  std::stringstream progName;
  progName << prog;
  ProgramOutCtx ctx(s, progName.str());
  std::vector<std::pair<Expr, Expr>>& palloc = ctx.d_progAlloc;
  // flatten its types, which will be processed until fix point below
  Expr p = prog;
  Expr pt = s.getTypeChecker().getType(p);
  Assert(pt.getKind() == Kind::PROGRAM_TYPE);
  for (size_t i = 0, nptargs = pt.getNumChildren(); i < nptargs; i++)
  {
    Expr ptc = pt[i];
    typeMap[ptc] = flattenEval(s, ctx, ptc);
  }
  toVisit.insert(toVisit.end(), palloc.begin(), palloc.end());
  palloc.clear();
  // process the main program body, unless this is a forward declaration.
  if (!progDef.isNull())
  {
    toVisit.emplace_back(prog, progDef);
  }
  std::pair<Expr, Expr> cur;
  do
  {
    cur = toVisit.back();
    Assert(ctx.getArgs().empty());
    Expr cprog = cur.first;
    Expr cdef = cur.second;
    Assert(cdef.getKind() == Kind::PROGRAM);
    // see if we need to purify each return term
    std::vector<Expr> newCases;
    bool caseChanged = false;
    for (size_t i = 0, ncases = cdef.getNumChildren(); i < ncases; i++)
    {
      Expr cret = cdef[i][1];
      Expr cretp = flattenEval(s, ctx, cret);
      if (cretp != cret)
      {
        caseChanged = true;
        Expr cPair = s.mkPair(cdef[i][0], cretp);
        newCases.push_back(cPair);
      }
      else
      {
        newCases.push_back(cdef[i]);
      }
    }
    if (caseChanged)
    {
      // update its definition in place.
      toVisit.pop_back();
      Expr newDef = s.mkExpr(Kind::PROGRAM, newCases);
      toVisit.emplace_back(cprog, newDef);
      Assert(!palloc.empty());
      // now process the programs we allocated.
      toVisit.insert(toVisit.end(), palloc.begin(), palloc.end());
      // clear them from the context
      palloc.clear();
    }
    else
    {
      Assert(palloc.empty());
      // it did not need processed, it is finished, add to final list.
      ret.push_back(cur);
      toVisit.pop_back();
    }
  } while (!toVisit.empty());
  return ret;
}

}  // namespace ethos
