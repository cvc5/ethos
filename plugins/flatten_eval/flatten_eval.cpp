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

ProgramOutCtx::ProgramOutCtx(size_t pcount)
    : d_varCount(0), d_progCount(pcount)
{

}

FlattenEval::FlattenEval(State& s) : StdPlugin(s) {}
FlattenEval::~FlattenEval() {}

void FlattenEval::flattenEval(State& s,
                              const Expr& pat,
                              const Expr& body,
                              std::ostream& os,
                              std::ostream& osp)
{
  size_t pcount = 0;
  ProgramOutCtx ctx(pcount);
  Assert(pat.getKind() == Kind::APPLY);
  Expr prog = pat[0];
  Expr progType = s.getTypeChecker().getType(prog);
  Assert(progType.getNumChildren() == pat.getNumChildren());
  for (size_t i = 1, nargs = pat.getNumChildren(); i < nargs; i++)
  {
    ctx.d_args.push_back(pat[i]);
    ctx.d_argTypes.push_back(progType[i - 1]);
  }
  flattenEvalInternal(s, ctx, body, os, osp);
  // update the global context
  pcount = ctx.d_progCount;
}

void FlattenEval::flattenEval(State& s,
                const Expr& t,
                std::ostream& os,
                std::ostream& osp)
{
  size_t pcount = 0;
  ProgramOutCtx ctx(pcount);
  // get the free variables, which will be the arguments
  std::vector<Expr> vars = Expr::getVariables(t);
  TypeChecker& tc = s.getTypeChecker();
  for (const Expr& v : vars)
  {
    Expr vv = v;
    Expr vt = tc.getType(vv);
    ctx.d_args.push_back(v);
    ctx.d_argTypes.push_back(vt);
  }
  flattenEvalInternal(s, ctx, t, os, osp);
  // update the global context
  pcount = ctx.d_progCount;
}

void FlattenEval::flattenEvalInternal(State& s,
                                  ProgramOutCtx& ctx,
                                  const Expr& t,
                                  std::ostream& os,
                                  std::ostream& osp)
{
  std::vector<Expr> newEvals;
  Expr bodyFinal = mkPurifyEvaluation(s, t, ctx, newEvals);
  while (!newEvals.empty())
  {
    size_t nnewEval = newEvals.size();
    for (size_t i=0; i<nnewEval; i++)
    {

    }
  }
  os << bodyFinal;
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
  size_t istart = (k == Kind::APPLY ? 1 : 0);
  size_t iend = (k == Kind::EVAL_IF_THEN_ELSE
                     ? 1
                     : (k == Kind::EVAL_REQUIRES ? 2 : e.getNumChildren()));
  for (size_t i = istart; i < iend; i++)
  {
    if (e[i].isEvaluatable())
    {
      // TODO: cache
      if (!isPure(e[i]))
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
  if (isPure(e) && ek!=Kind::EVAL_IF_THEN_ELSE && ek!=Kind::EVAL_REQUIRES)
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
        ctx.d_varCount++;
        std::stringstream ss;
        ss << "$eo_" << ctx.d_varCount;
        Expr curt = s.getTypeChecker().getType(cur);
        Assert(!curt.isNull()) << "Failed to type check " << cur;
        Expr v = s.mkSymbol(Kind::PARAM, ss.str(), curt);
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
