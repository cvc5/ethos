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
  std::vector<std::pair<Expr, Expr>> ret;
  // TODO
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
      std::stringstream ss;
      ss << "$eov_" << pat << "." << it->second;
      it->second++;
      // FIXME: get type
      Expr patType;
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
      return s.mkExpr(pat.getKind(), nchildren);
    }
  }
  // TODO
  return pat;
}


}  // namespace ethos
