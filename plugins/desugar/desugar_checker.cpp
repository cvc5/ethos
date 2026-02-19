/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "desugar_checker.h"

#include <sstream>
#include <string>

#include "desugar.h"
#include "state.h"

namespace ethos {

DesugarChecker::DesugarChecker(State& s, Desugar* d) : StdPlugin(s), d_desugar(d)
{
  d_true = d_state.mkTrue();
  d_boolType = d_state.mkBoolType();
}

DesugarChecker::~DesugarChecker() {}

void DesugarChecker::finalizeRule(const Expr& v)
{
  d_rules << "(declare-const $smd_rule." << v << " $eo_Rule)" << std::endl;
  AppInfo* ainfo = d_state.getAppInfo(v.getValue());
  Expr tupleVal = ainfo->d_attrConsTerm;
  Assert(tupleVal.getNumChildren() == 4);
  Expr plCons;
  if (tupleVal[0].getKind()!=Kind::ANY)
  {
    plCons = tupleVal[0];
  }
  bool isAssume = tupleVal[1]==d_true;
  bool isConcExplicit = tupleVal[2]==d_true;
  Expr rprog = tupleVal[3];
}

void DesugarChecker::printTerm(const Expr& e, std::ostream& os)
{
  d_desugar->printTerm(e, os);
}

}  // namespace ethos
