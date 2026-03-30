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

std::string smtIndex(size_t i)
{
  std::stringstream ss;
  ss << "($smt_apply_0 \"" << i << "\")";
  return ss.str();
}

DesugarChecker::DesugarChecker(State& s, Desugar* d)
    : StdPlugin(s), d_desugar(d)
{
  d_true = d_state.mkTrue();
  d_boolType = d_state.mkBoolType();
}

DesugarChecker::~DesugarChecker() {}

void DesugarChecker::finalizeRule(const Expr& v)
{
  std::stringstream embArg;
  std::stringstream macroArg;
  std::stringstream macroRet;
  std::stringstream invokePat;
  std::stringstream invokeRet;
  std::stringstream progParamList;
  std::stringstream progSig;
  std::stringstream progPat;
  std::stringstream progRet;

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
    embArg << " (T" << i << " Type :implicit) (x" << i << " T" << i
           << " :opaque)";
    macroArg << " (T" << i << " Type :implicit) (x" << i << " T" << i << ")";
    macroRet << " x" << i;
    invokeRet << " a" << i;
    progParamList << " (T" << i << " Type) (a" << i << " T" << i << ")";
    progSig << " T" << i;
    progPat << " a" << i;
    progRet << " a" << i;
    std::stringstream ssnext;
    ssnext << "($eot_alc a" << (nargs - i) + 1 << " " << invPatArgs << ")";
    invPatArgs = ssnext.str();
  }
  invokePat << " " << invPatArgs;
  // then, pass the assumption
  if (isAssume)
  {
    progRet << " A";
    invokePat << " A";
    invokeRet << " A";
  }
  // then the premises
  if (!plCons.isNull())
  {
    // combine the premises if :premise-list
    Assert(npremises == 1);
    embArg << " (premises $eo_IndexList :opaque)";
    macroArg << " (premises $eo_IndexList)";
    macroRet << " premises";
    invokePat << " premises";
    invokeRet << " ($eo_pf ($eo_mk_premise_list " << plCons << " premises S))";
    progParamList << " (pl $eo_Proof)";
    progSig << " $eo_Proof";
    progPat << " pl";
    progRet << " pl";
  }
  else
  {
    Assert(npremises <= 8)
        << "Compiler supports at most 8 premises to proof rule";
    std::string invPatPremises = "$eot_iln";
    for (size_t i = 1; i <= npremises; i++)
    {
      embArg << " (n" << i << " $eoT_Index :opaque)";
      macroArg << " (n" << i << " $eoT_Index)";
      macroRet << " n" << i;
      invokeRet << " ($eo_pf ($eo_state_proven_nth S n" << i << "))";
      progParamList << " (p" << i << " $eo_Proof)";
      progSig << " $eo_Proof";
      progPat << " p" << i;
      progRet << " p" << i;
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
  std::stringstream ssr;
  ssr << "$rule_" << vname;
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

void DesugarChecker::printTerm(const Expr& e, std::ostream& os)
{
  d_desugar->printTerm(e, os);
}

void DesugarChecker::finalizeChecker(const std::string& finalEo)
{
  std::string outPath =
      getOutputPath("plugins/desugar/eo_desugar_checker_gen.eo");
  std::cout << "Write checker-defs    " << outPath << std::endl;
  std::ofstream outec(outPath);
  // include signature
  outec << finalEo;
  // then include the checker definition
  output(outec);
  outec << std::endl;
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
  replace(finalCheckEo, "$EO_INVOKE_DEFS$", d_ruleInvokesDefs.str());
  out << finalCheckEo;
  out << ";; ------------ checker end" << std::endl;
}

}  // namespace ethos
