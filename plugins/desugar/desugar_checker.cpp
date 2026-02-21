/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "desugar_checker.h"

#include <fstream>
#include <sstream>
#include <string>

#include "desugar.h"
#include "state.h"

namespace ethos {

DesugarChecker::DesugarChecker(State& s, Desugar* d)
    : StdPlugin(s), d_desugar(d)
{
  d_true = d_state.mkTrue();
  d_boolType = d_state.mkBoolType();
}

DesugarChecker::~DesugarChecker() {}

void DesugarChecker::finalizeRule(const Expr& v)
{
  std::stringstream ssr;
  ssr << "$emb_rule." << v;
  d_rules << "(declare-const " << ssr.str() << " $eo_Rule)" << std::endl;
  AppInfo* ainfo = d_state.getAppInfo(v.getValue());
  Expr tupleVal = ainfo->d_attrConsTerm;
  Assert(tupleVal.getNumChildren() == 4);
  Expr plCons;
  if (tupleVal[0].getKind() != Kind::ANY)
  {
    plCons = tupleVal[0];
  }
  bool isAssume = tupleVal[1] == d_true;
  bool isConcExplicit = tupleVal[2] == d_true;
  Expr rprog = tupleVal[3];
  std::stringstream argList;
  Expr rprogType = rprog.getType();
  size_t nargs = 0;
  size_t npremises = 0;
  std::stringstream ret, retEnd;
  if (rprogType.getKind() == Kind::PROGRAM_TYPE)
  {
    Expr pfType = d_state.mkProofType();
    for (size_t i = 1, nchild = rprogType.getNumChildren(); i < nchild; i++)
    {
      Expr argType = rprogType[i - 1];
      if (argType == pfType)
      {
        npremises++;
      }
      else
      {
        nargs++;
      }
    }
  }
  d_ruleInvokes << "  (($eo_invoke_step " << ssr.str() << " proven ";
  // if it is not an assume rule, we must not have provided an assumption
  d_ruleInvokes << (isAssume ? "assump " : "$eo_NullBool ");
  std::stringstream invokeArgs;
  // subtract an ordinary argument if conclusion explicit
  if (isConcExplicit)
  {
    Assert(nargs > 0);
    nargs--;
  }
  // first, pass the ordinary arguments
  if (nargs > 0)
  {
    Assert(nargs <= 10);
    d_ruleInvokes << "($eo_alist_cons";
    for (size_t i = 0; i < nargs; i++)
    {
      d_ruleInvokes << " a" << (i + 1);
      invokeArgs << " a" << (i + 1);
    }
    d_ruleInvokes << ") ";
  }
  else
  {
    d_ruleInvokes << "$eo_alist_nil ";
  }
  if (isConcExplicit)
  {
    invokeArgs << " proven";
    ret << "(eo::requires (eo::eq proven $eo_NullBool) false ";
    retEnd << ")";
  }
  // then, pass the assumption
  if (isAssume)
  {
    Assert(npremises > 0);
    npremises--;
    invokeArgs << " ($eo_pf assump)";
    ret << "(eo::requires (eo::eq assump $eo_NullBool) false ";
    retEnd << ")";
  }
  // then the premises
  if (!plCons.isNull())
  {
    // combine the premises if :premise-list
    Assert(npremises == 1);
    d_ruleInvokes << "premises ";
    invokeArgs << " ($eo_pf ($eo_mk_premise_list " << plCons << " premises S))";
  }
  else
  {
    if (npremises > 0)
    {
      Assert(npremises <= 8);
      d_ruleInvokes << "($eo_plist_cons";
      for (size_t i = 0; i < npremises; i++)
      {
        d_ruleInvokes << " n" << (i + 1);
        invokeArgs << " ($eo_pf ($eo_State_proven S n" << (i + 1) << "))";
      }
      d_ruleInvokes << ")";
    }
    else
    {
      d_ruleInvokes << "$eo_plist_nil ";
    }
  }
  d_ruleInvokes << "S) ";
  if (invokeArgs.str().empty())
  {
    Assert(npremises == 0 && nargs == 0);
    ret << rprog;
  }
  else
  {
    ret << "(" << rprog << invokeArgs.str() << ")";
  }
  ret << retEnd.str();
  d_ruleInvokes << ret.str() << ")" << std::endl;
}

void DesugarChecker::printTerm(const Expr& e, std::ostream& os)
{
  d_desugar->printTerm(e, os);
}

void DesugarChecker::finalizeChecker(const std::string& finalEo)
{
  // auto-generate the checker as well
  std::stringstream ssiec;
  ssiec << s_plugin_path << "plugins/desugar/eo_desugar_checker.eo";
  std::ifstream inec(ssiec.str());
  std::ostringstream ssec;
  ssec << inec.rdbuf();
  std::string finalCheckEo = ssec.str();
  replace(finalCheckEo, "$EO_RULE_DEFS$", d_rules.str());
  replace(finalCheckEo, "$EO_RULE_INVOKE$", d_ruleInvokes.str());

  std::stringstream ssoec;
  ssoec << s_plugin_path << "plugins/desugar/eo_desugar_checker_gen.eo";
  std::cout << "Write checker-defs    " << ssoec.str() << std::endl;
  std::ofstream outec(ssoec.str());
  // include signature
  outec << finalEo;
  // then include the checker definition
  outec << finalCheckEo;
  outec << std::endl;
}

}  // namespace ethos
