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

#include "state.h"

namespace ethos {

DesugarChecker::DesugarChecker(State& s) : StdPlugin(s)
{
  d_true = d_state.mkTrue();
}

DesugarChecker::~DesugarChecker() {}

void DesugarChecker::finalizeRule(const Expr& v)
{
  std::stringstream invokePat;
  std::stringstream invokeRet;

  AppInfo* ainfo = d_state.getAppInfo(v.getValue());
  Expr tupleVal = ainfo->d_attrConsTerm;
  Assert(tupleVal.getNumChildren() == 4);
  Expr plCons;
  if (tupleVal[0].getKind() != Kind::ANY)
  {
    plCons = tupleVal[0];
  }
  bool isAssume = tupleVal[1] == d_true;
  // conclusion explicit is compiled away when desugaring proof
  // bool isConcExplicit = tupleVal[2] == d_true;
  Expr rprog = tupleVal[3];
  Expr rprogType = rprog.getType();
  size_t nargs = 0;
  size_t npremises = 0;
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
  // assumption is an ordinary argument
  if (isAssume)
  {
    Assert(nargs > 0);
    nargs--;
  }
  // first, pass the ordinary arguments
  Assert(nargs <= 10) << "Compiler supports at most 10 arguments to proof rule";
  std::string invPatArgs = "$eot_aln";
  for (size_t i = 1; i <= nargs; i++)
  {
    invokeRet << " a" << i;
    std::stringstream ssnext;
    ssnext << "($eot_alc a" << (nargs - i) + 1 << " " << invPatArgs << ")";
    invPatArgs = ssnext.str();
  }
  invokePat << " " << invPatArgs;
  // then, pass the assumption
  if (isAssume)
  {
    invokePat << " A";
    invokeRet << " A";
  }
  // then the premises
  if (!plCons.isNull())
  {
    // combine the premises if :premise-list
    Assert(npremises == 1);
    invokePat << " premises";
    invokeRet << " ($eo_pf ($eo_mk_premise_list " << plCons << " premises S))";
  }
  else
  {
    Assert(npremises <= 8)
        << "Compiler supports at most 8 premises to proof rule";
    std::string invPatPremises = "$eot_iln";
    for (size_t i = 1; i <= npremises; i++)
    {
      invokeRet << " ($eo_pf ($eo_state_proven_nth S n" << i << "))";
      std::stringstream ssnext;
      ssnext << "($eot_ilc n" << (npremises - i) + 1 << " " << invPatPremises
             << ")";
      invPatPremises = ssnext.str();
    }
    invokePat << " " << invPatPremises;
  }
  std::stringstream ssv;
  ssv << v;
  std::string vname = ssv.str();
  vname = replace_all(vname, "-", "_");
  std::ostream* rout = isAssume ? &d_ruleInvokesPop : &d_ruleInvokes;
  d_rules << "(declare-const $emb_r." << vname << " $eo_Rule)" << std::endl;
  (*rout) << "  (($eo_cmd_step_" << (isAssume ? "pop_" : "")
          << "proven S $emb_r." << vname << invokePat.str() << ") ";
  if (!invokeRet.str().empty())
  {
    (*rout) << "(" << rprog << invokeRet.str() << ")";
  }
  else
  {
    (*rout) << rprog;
  }
  (*rout) << ")" << std::endl;
}

void DesugarChecker::output(std::ostream& out)
{
  out << ";; ------------ checker" << std::endl;
  // auto-generate the checker as well
  std::ifstream inec(getResourcePath("plugins/desugar/eo_desugar_checker.eo"));
  std::ostringstream ssec;
  ssec << inec.rdbuf();
  std::string finalCheckEo = ssec.str();
  replace(finalCheckEo, "$EO_RULE_DEFS$", d_rules.str());
  replace(finalCheckEo, "$EO_INVOKE$", d_ruleInvokes.str());
  replace(finalCheckEo, "$EO_INVOKE_POP$", d_ruleInvokesPop.str());
  out << finalCheckEo;
  out << ";; ------------ checker end" << std::endl;
}

}  // namespace ethos
