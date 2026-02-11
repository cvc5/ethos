/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "linear_patterns.h"
#include "state.h"

namespace ethos {

LinearPattern::LinearPattern(State& s) : StdPlugin(s) {}

LinearPattern::~LinearPattern() {}

std::vector<std::pair<Expr, Expr>> LinearPattern::linearize(
    State& s,
    const Expr& prog,
    const Expr& progDef)
{
  Assert (!progDef.isNull() && progDef.getKind()==Kind::PROGRAM);
  std::vector<std::pair<Expr, Expr>> ret;
  std::vector<Expr> currCases;
  Expr currProg = prog;
  size_t progCount = 0;
  Expr ptype = prog.getType();
  for (size_t i=0, ncases = progDef.getNumChildren(); i<ncases; i++)
  {
    Assert (progDef[i].getKind()==Kind::TUPLE && progDef[i].getNumChildren()==2);
    Expr pat = progDef[i][0];
    std::pair<Expr, Expr> lpat = linearizePattern(s, pat);
    if (lpat.second.isNull())
    {
      currCases.push_back(progDef[i]);
      continue;
    }
    // make a new copy of the program
    progCount++;
    std::stringstream ss;
    ss << "$eo.l." << progCount << "." << prog;
    Expr newProg = s.mkSymbol(Kind::PROGRAM_CONST, ss.str(), ptype);
    std::vector<Expr> newappc;
    std::vector<Expr> defappc;
    newappc.push_back(newProg);
    for (size_t j=1, ncallArgs=pat.getNumChildren(); j<ncallArgs; j++)
    {
      newappc.push_back(pat[j]);
      std::stringstream ssd;
      ssd << "$eo.dv." << j;
      defappc.push_back(s.mkSymbol(Kind::PARAM, ssd.str(), pat[j].getType()));
    }
    Expr newApp = s.mkExprSimple(Kind::APPLY, newappc);
    Expr defApp = s.mkExprSimple(Kind::APPLY, defappc);
    Expr retLin = s.mkExpr(Kind::EVAL_IF_THEN_ELSE, {lpat.second, progDef[i][1], newApp});
    Expr linCase = s.mkPair(lpat.first, retLin);
    currCases.push_back(linCase);
    Expr defCase = s.mkPair(defApp, newApp);
    currCases.push_back(defCase);
    Expr currProgDef = s.mkExprSimple(Kind::PROGRAM, currCases);
    ret.emplace_back(currProg, currProgDef);
    currProg = newProg;
    currCases.clear();
  }
  if (currProg==prog)
  {
    ret.emplace_back(prog, progDef);
  }
  else
  {
    // otherwise finish with remainder
    Expr currProgDef = s.mkExprSimple(Kind::PROGRAM, currCases);
    ret.emplace_back(currProg, currProgDef);
  }
  return ret;
}

std::pair<Expr, Expr> LinearPattern::linearizePattern(State& s, const Expr& pat)
{
  std::map<Expr, size_t> params;
  std::vector<Expr> conds;
  Expr lpat = linearizeRec(s, pat, params, conds);
  if (conds.empty())
  {
    Assert (lpat==pat);
    Expr nullExpr;
    return std::pair<Expr, Expr>(lpat, nullExpr);
  }
  if (conds.size()==1)
  {
    return std::pair<Expr, Expr>(lpat, conds[0]);
  }
  Expr cond = s.mkExpr(Kind::EVAL_AND, conds);
  return std::pair<Expr, Expr>(lpat, cond);
}

Expr LinearPattern::linearizeRec(State& s, const Expr& pat, std::map<Expr, size_t>& params, std::vector<Expr>& conds)
{
  if (pat.getKind()==Kind::PARAM)
  {
    std::map<Expr, size_t>::iterator it = params.find(pat);
    if (it==params.end())
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
  else if (pat.getNumChildren()>0)
  {
    std::vector<Expr> nchildren;
    bool childChanged = false;
    for (size_t i=0, nchild = pat.getNumChildren(); i<nchild; i++)
    {
      Expr ns = linearizeRec(s, pat[i], params, conds);
      nchildren.push_back(ns);
      childChanged = childChanged || pat[i]!=ns;
    }
    if (childChanged)
    {
      return s.mkExprSimple(pat.getKind(), nchildren);
    }
  }
  return pat;
}


}  // namespace ethos
