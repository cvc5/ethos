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

ProgramOutCtx::ProgramOutCtx(State& s, size_t pcount)
    : d_state(s), d_progPrefix("$eop_"), d_varCount(0), d_progCount(pcount)
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
  Assert (!d_args.empty());
  d_args.pop_back();
  d_argTypes.pop_back();
}

Expr ProgramOutCtx::allocateProgram(const std::vector<Expr>& nvars, const std::vector<Expr>& nargs, const Expr& ret)
{
  Assert (nvars.size()==nargs.size());
  size_t numVars = nvars.size();
  for (size_t i=0; i<numVars; i++)
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
  for (size_t i=0; i<numVars; i++)
  {
    popArg();
  }
  std::vector<Expr> pappChildren;
  pappChildren.push_back(prog);
  pappChildren.insert(pappChildren.end(), d_args.begin(), d_args.end());
  for (size_t i=0; i<numVars; i++)
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
  ss << d_progPrefix << d_progCount;
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
  if (k==Kind::EVAL_IF_THEN_ELSE)
  {
    Expr et = getTypeInternal(e);
    Expr btrue = d_state.mkTrue();
    Expr prog;
    std::vector<Expr> pcs;
    for (size_t i=0; i<2; i++)
    {
      Expr bvalue = d_state.mkBool(i==0);
      Expr progRet = i==0 ? e[1] : e[2];
      // should have already ensured branches are pure
      Assert (FlattenEval::isPure(progRet));
      pushArg(bvalue);
      if (i==0)
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
  else if (k==Kind::EVAL_REQUIRES)
  {
    // should have already ensured the return is pure.
    Assert (FlattenEval::isPure(e[2]));
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

Expr FlattenEval::flattenEval(State& s,
                              ProgramOutCtx& ctx,
                              const Expr& pat,
                              const Expr& body)
{
  Assert(pat.getKind() == Kind::APPLY);
  Expr prog = pat[0];
  Expr progType = s.getTypeChecker().getType(prog);
  Assert(progType.getNumChildren() == pat.getNumChildren());
  for (size_t i = 1, nargs = pat.getNumChildren(); i < nargs; i++)
  {
    ctx.pushArgTyped(pat[i], progType[i - 1]);
  }
  return flattenEvalInternal(s, ctx, body);
}

Expr FlattenEval::flattenEval(State& s,
                              ProgramOutCtx& ctx,
                              const Expr& t)
{
  // get the free variables, which will be the arguments
  // to potential programs
  std::vector<Expr> vars = Expr::getVariables(t);
  for (const Expr& v : vars)
  {
    ctx.pushArg(v);
  }
  return flattenEvalInternal(s, ctx, t);
}

Expr FlattenEval::flattenEvalInternal(State& s,
                                      ProgramOutCtx& ctx,
                                      const Expr& t)
{
  std::map<Expr, Expr>& visited = ctx.d_visited;
  std::map<Expr, std::vector<Expr>> newEvals;
  std::map<Expr, std::vector<Expr>>::iterator itp;
  std::vector<Expr> toVisit;
  toVisit.emplace_back(t);
  Expr curTerm;
  do
  {
    Expr prevTerm = curTerm;
    curTerm = toVisit.back();
    itp = newEvals.find(curTerm);
    if (itp==newEvals.end())
    {
      std::vector<Expr>& nevals = newEvals[curTerm];
      Expr curTermPurify = mkPurifyEvaluation(s, curTerm, ctx, nevals);
      if (curTermPurify==curTerm)
      {
        Assert (nevals.empty());
        toVisit.pop_back();
        continue;
      }
      Assert (!nevals.empty());
      // push a context change
      for (size_t i = 0, nnewEval = nevals.size(); i < nnewEval; i++)
      {
        Expr ceval = nevals[i];
        Expr cvar = visited[ceval];
        Assert(!cvar.isNull() && cvar.getKind() == Kind::PARAM);
        ctx.pushArg(cvar);
      }
      toVisit.emplace_back(curTermPurify);
      //Expr prog = ctx.allocateProgram(curTermT);
      continue;
    }
    Assert (!prevTerm.isNull());
    toVisit.pop_back();
    std::vector<Expr>& nevals = itp->second;
    std::vector<Expr> nvars;
    for (size_t i = 0, nnewEval = nevals.size(); i < nnewEval; i++)
    {
      Expr ceval = nevals[i];
      Expr cvar = visited[ceval];
      nvars.push_back(cvar);
      ctx.popArg();
    }
    // call allocate program, which will allocate the program and
    // return the call.
    curTerm = ctx.allocateProgram(nvars, nevals, prevTerm);
  } while (!toVisit.empty());
  Assert (visited.find(t)!=visited.end());
  return visited[t];
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
  size_t iend = (k == Kind::EVAL_IF_THEN_ELSE
                     ? 1
                     : (k == Kind::EVAL_REQUIRES ? 2 : e.getNumChildren()));
  for (size_t i = istart; i < iend; i++)
  {
    if (e[i].isEvaluatable())
    {
      Kind ek = e[i].getKind();
      // TODO: cache
      // requires or ite as strict children are not allowed
      if (ek==Kind::EVAL_IF_THEN_ELSE || ek==Kind::EVAL_REQUIRES || !isPure(e[i]))
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
  Kind ek = e.getKind();
  if (isPure(e) && ek != Kind::EVAL_IF_THEN_ELSE && ek != Kind::EVAL_REQUIRES)
  {
    // if it is already pure, we are done
    // note that ite and requires still require processing
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
      size_t iend =
          (k == Kind::EVAL_IF_THEN_ELSE
               ? 1
               : (k == Kind::EVAL_REQUIRES ? 2 : cur.getNumChildren()));
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

}  // namespace ethos
