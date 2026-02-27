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
  // first, pass the ordinary arguments
  Assert(nargs <= 10);
  for (size_t i = 1; i <= nargs; i++)
  {
    embArg << " (T" << i << " Type :implicit) (x" << i << " T" << i
           << " :opaque)";
    macroArg << " (T" << i << " Type :implicit) (x" << i << " T" << i << ")";
    macroRet << " x" << i;
    invokePat << " a" << i;
    invokeRet << " a" << i;
    progParamList << " (T" << i << " Type :implicit) (a" << i << " T" << i
                  << ")";
    progSig << " T" << i;
    progPat << " a" << i;
    progRet << " a" << i;
  }
  // then, pass the assumption
  if (isAssume)
  {
    Assert(npremises > 0);
    npremises--;
    progRet << " ($eo_pf assume)";
  }
  // then the premises
  if (!plCons.isNull())
  {
    // combine the premises if :premise-list
    Assert(npremises == 1);
    embArg << " (premises $eo_PList :opaque)";
    macroArg << " (premises $eo_PList)";
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
    Assert(npremises <= 8);
    for (size_t i = 1; i <= npremises; i++)
    {
      embArg << " (n" << i << " $eo_Index :opaque)";
      macroArg << " (n" << i << " $eo_Index)";
      macroRet << " n" << i;
      invokePat << " n" << i;
      invokeRet << " ($eo_pf ($eo_state_proven_nth S n" << i << "))";
      progParamList << " (p" << i << " $eo_Proof)";
      progSig << " $eo_Proof";
      progPat << " p" << i;
      progRet << " p" << i;
    }
  }

  std::stringstream ssr;
  ssr << "$cmd_" << v;
  d_rules << "(declare-parameterized-const $emb_cmd." << v << " ("
          << embArg.str() << ") $eo_Cmd)" << std::endl;
  d_rules << "(define " << ssr.str() << " (" << macroArg.str() << ") ";
  if (!macroRet.str().empty())
  {
    d_rules << "($emb_cmd." << v << macroRet.str() << "))" << std::endl;
  }
  else
  {
    d_rules << "$emb_cmd." << v << std::endl;
  }
  d_ruleInvokes << "  (($eo_invoke_cmd S ($cmd_" << v << invokePat.str()
                << ")) ";
  if (isAssume)
  {
    d_ruleInvokes << "($eo_invoke_cmd_pop_" << v << " S" << invokeRet.str()
                  << "))" << std::endl;
    std::stringstream pname;
    pname << "$eo_invoke_cmd_pop_" << v;
    d_ruleInvokesDefs << "(program " << pname.str() << std::endl;
    d_ruleInvokesDefs << "  ((assume F) (s $eo_State) (so $eo_StateObj)"
                      << progParamList.str() << ")" << std::endl;
    d_ruleInvokesDefs << "  :signature ($eo_State" << progSig.str()
                      << ") $eo_State" << std::endl;
    d_ruleInvokesDefs << "  (" << std::endl;
    d_ruleInvokesDefs << "  ((" << pname.str()
                      << " ($s_cons ($so_assume_push F) s)" << progPat.str()
                      << ")" << std::endl;
    d_ruleInvokesDefs << "     ($eo_push_proven (" << rprog << progRet.str()
                      << ") s))" << std::endl;
    d_ruleInvokesDefs << "  ((" << pname.str() << " ($s_cons so s)"
                      << progPat.str() << ") " << std::endl;
    d_ruleInvokesDefs << "     (" << pname.str() << " s" << progPat.str()
                      << "))" << std::endl;
    d_ruleInvokesDefs << "  ((" << pname.str() << " s" << progPat.str()
                      << ") $s_fail)" << std::endl;
    d_ruleInvokesDefs << "  )" << std::endl;
    d_ruleInvokesDefs << ")" << std::endl;
  }
  else
  {
    d_ruleInvokes << "($eo_push_proven ";
    if (!invokeRet.str().empty())
    {
      d_ruleInvokes << "(" << rprog << invokeRet.str() << ")";
    }
    else
    {
      d_ruleInvokes << rprog;
    }
    d_ruleInvokes << " S))" << std::endl;
  }
}

void DesugarChecker::printTerm(const Expr& e, std::ostream& os)
{
  d_desugar->printTerm(e, os);
}

void DesugarChecker::finalizeChecker(const std::string& finalEo)
{
  std::stringstream ssoec;
  ssoec << s_plugin_path << "plugins/desugar/eo_desugar_checker_gen.eo";
  std::cout << "Write checker-defs    " << ssoec.str() << std::endl;
  std::ofstream outec(ssoec.str());
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
  std::stringstream ssiec;
  ssiec << s_plugin_path << "plugins/desugar/eo_desugar_checker.eo";
  std::ifstream inec(ssiec.str());
  std::ostringstream ssec;
  ssec << inec.rdbuf();
  std::string finalCheckEo = ssec.str();
  replace(finalCheckEo, "$EO_CMD_DEFS$", d_rules.str());
  replace(finalCheckEo, "$EO_INVOKE$", d_ruleInvokes.str());
  replace(finalCheckEo, "$EO_INVOKE_DEFS$", d_ruleInvokesDefs.str());
  out << finalCheckEo;
  out << ";; ------------ checker end" << std::endl;
}

}  // namespace ethos
