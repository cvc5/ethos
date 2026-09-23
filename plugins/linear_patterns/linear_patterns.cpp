/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "linear_patterns.h"

#include <algorithm>
#include <sstream>

#include "state.h"

namespace ethos {

std::vector<std::pair<Expr, Expr>> LinearPattern::linearize(State& s,
                                                            const Expr& prog,
                                                            const Expr& progDef)
{
  Assert(!progDef.isNull() && progDef.getKind() == Kind::PROGRAM);
  std::vector<std::pair<Expr, Expr>> ret;
  std::vector<Expr> currCases;
  Expr currProg = prog;
  size_t progCount = 0;
  Expr ptype = prog.getType();
  for (size_t i = 0, ncases = progDef.getNumChildren(); i < ncases; i++)
  {
    Assert(progDef[i].getKind() == Kind::TUPLE
           && progDef[i].getNumChildren() == 2);
    Expr pat = progDef[i][0];
    std::pair<Expr, Expr> lpat = linearizePattern(s, pat);
    if (lpat.second.isNull())
    {
      currCases.push_back(
          s.mkPair(mkCasePattern(s, currProg, pat), progDef[i][1]));
      continue;
    }
    if (i + 1 == ncases)
    {
      // as an optimization, just do a requires if we are the last case
      Expr ctrue = s.mkTrue();
      Expr guardedRet =
          s.mkExpr(Kind::EVAL_REQUIRES, {lpat.second, ctrue, progDef[i][1]});
      currCases.push_back(
          s.mkPair(mkCasePattern(s, currProg, lpat.first), guardedRet));
      continue;
    }
    // make a new copy of the program
    progCount++;
    std::stringstream ss;
    ss << "$eo.l." << progCount << "." << prog;
    Expr newProg = s.mkSymbol(Kind::PROGRAM_CONST, ss.str(), ptype);
    std::vector<Expr> newappc;
    std::vector<Expr> defappc;
    defappc.push_back(currProg);
    newappc.push_back(newProg);
    bool wasDefault = true;
    for (size_t j = 1, ncallArgs = lpat.first.getNumChildren(); j < ncallArgs;
         j++)
    {
      wasDefault = wasDefault && lpat.first[j].getKind() == Kind::PARAM;
      newappc.push_back(lpat.first[j]);
      std::stringstream ssd;
      ssd << "$eo.dv." << j;
      defappc.push_back(s.mkSymbol(Kind::PARAM, ssd.str(), pat[j].getType()));
    }
    Expr newApp = s.mkExpr(Kind::APPLY, newappc);
    Expr retLin =
        s.mkExpr(Kind::EVAL_IF_THEN_ELSE, {lpat.second, progDef[i][1], newApp});
    Expr linCase = s.mkPair(mkCasePattern(s, currProg, lpat.first), retLin);
    currCases.push_back(linCase);
    // only needs a default if the linearized case was not already fully general
    if (!wasDefault)
    {
      Expr defApp = s.mkExpr(Kind::APPLY, defappc);
      defappc[0] = newProg;
      Expr defRet = s.mkExpr(Kind::APPLY, defappc);
      Expr defCase = s.mkPair(defApp, defRet);
      currCases.push_back(defCase);
    }
    Expr currProgDef = s.mkExpr(Kind::PROGRAM, currCases);
    ret.emplace_back(currProg, currProgDef);
    currProg = newProg;
    currCases.clear();
  }
  // finish with remainder
  Expr currProgDef = s.mkExpr(Kind::PROGRAM, currCases);
  ret.emplace_back(currProg, currProgDef);
  std::reverse(ret.begin(), ret.end());
  return ret;
}

Expr LinearPattern::mkCasePattern(State& s, const Expr& prog, const Expr& pat)
{
  Assert(pat.getKind() == Kind::APPLY && pat.getNumChildren() > 0);
  if (pat[0] == prog)
  {
    return pat;
  }
  std::vector<Expr> children;
  children.push_back(prog);
  for (size_t i = 1, nchild = pat.getNumChildren(); i < nchild; i++)
  {
    children.push_back(pat[i]);
  }
  // note we do not desugar here, see linearizeRec below
  return s.mkRawExpr(Kind::APPLY, children);
}

std::pair<Expr, Expr> LinearPattern::linearizePattern(State& s, const Expr& pat)
{
  std::map<Expr, size_t> params;
  std::vector<Expr> conds;
  Expr lpat = linearizeRec(s, pat, params, conds);
  if (conds.empty())
  {
    Assert(lpat == pat);
    Expr nullExpr;
    return std::pair<Expr, Expr>(lpat, nullExpr);
  }
  if (conds.size() == 1)
  {
    return std::pair<Expr, Expr>(lpat, conds[0]);
  }
  Expr cond = s.mkExpr(Kind::EVAL_AND, conds);
  return std::pair<Expr, Expr>(lpat, cond);
}

Expr LinearPattern::linearizeRec(State& s,
                                 const Expr& pat,
                                 std::map<Expr, size_t>& params,
                                 std::vector<Expr>& conds)
{
  if (pat.getKind() == Kind::PARAM)
  {
    std::map<Expr, size_t>::iterator it = params.find(pat);
    if (it == params.end())
    {
      params[pat] = 1;
    }
    else
    {
      it->second++;
      std::stringstream ss;
      ss << "$eo.lv." << pat << "." << it->second;
      Expr patType = pat.getType();
      Expr npat = s.mkSymbol(Kind::PARAM, ss.str(), patType);
      Expr cond = s.mkExpr(Kind::EVAL_EQ, {pat, npat});
      conds.push_back(cond);
      return npat;
    }
  }
  else if (pat.getNumChildren() > 0)
  {
    std::vector<Expr> nchildren;
    bool childChanged = false;
    for (size_t i = 0, nchild = pat.getNumChildren(); i < nchild; i++)
    {
      Expr ns = linearizeRec(s, pat[i], params, conds);
      nchildren.push_back(ns);
      childChanged = childChanged || pat[i] != ns;
    }
    if (childChanged)
    {
      // Note we construct the term without desugaring, since pat has already
      // been desugared by the parser. In particular, using mkExpr here would
      // reapply the constructor attributes of the head of an application, e.g.
      // it would append a second nil terminator to a :right-assoc-nil
      // application. This mirrors how TypeChecker::evaluate reconstructs
      // terms.
      return s.mkRawExpr(pat.getKind(), nchildren);
    }
  }
  return pat;
}

}  // namespace ethos
