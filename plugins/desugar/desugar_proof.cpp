/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "desugar_proof.h"

#include <fstream>
#include <sstream>
#include <string>

#include "desugar.h"
#include "state.h"

namespace ethos {

DesugarProof::DesugarProof(State& s, Desugar* d) : StdPlugin(s), d_desugar(d)
{
  d_true = d_state.mkTrue();
  d_boolType = d_state.mkBoolType();
  d_currTimestamp = 0;
}

DesugarProof::~DesugarProof() {}

void DesugarProof::output(std::ostream& out) { out << d_eoPfSteps.str(); }

void DesugarProof::notifyAssume(const std::string& name,
                                Expr& proven,
                                bool isPush)
{
  d_cmds << "(define $eo_p_" << name << " () ($cmd_assume";
  if (isPush)
  {
    d_cmds << "_push";
    d_timestampScope.push_back(d_currTimestamp);
  }
  d_cmds << " ";
  printTerm(proven, d_cmds);
  d_cmds << "))";


  d_eoPfSteps << "(define $eo_p_" << name << " () ";
  printTerm(proven, d_eoPfSteps);
  // d_eoPfSteps << " :type Bool";
  d_eoPfSteps << ")" << std::endl;
}

bool DesugarProof::notifyStep(const std::string& name,
                              Expr& rule,
                              Expr& proven,
                              const std::vector<Expr>& premises,
                              const std::vector<Expr>& args,
                              bool isPop,
                              Expr& result,
                              std::ostream* err)
{

  if (isPop)
  {
    Assert (!d_timestampScope.empty());
    d_currTimestamp = d_timestampScope.back();
    d_timestampScope.pop_back();
  }

  AppInfo* ainfo = d_state.getAppInfo(rule.getValue());
  Expr tupleVal = ainfo->d_attrConsTerm;
  Assert(tupleVal.getNumChildren() == 4);
  Expr plCons;
  if (tupleVal[0].getKind() != Kind::ANY)
  {
    plCons = tupleVal[0];
  }
  // is assume is part of the checker compilation
  //bool isAssume = tupleVal[1] == d_true;
  bool isConcExplicit = tupleVal[2] == d_true;

  d_cmds << "(define $eo_p_" << name << " () ($cmd_" << rule;
  for (size_t i=0, nargs = args.size(); i<nargs; i++)
  {
    d_cmds << " ";
    printTerm(args[i], d_cmds);
  }
  if (isConcExplicit)
  {
    d_cmds << " ";
    printTerm(proven, d_cmds);
  }
  if (!plCons.isNull())
  {
    std::string ret = "$eo_plist_nil";
    for (size_t i=0, npremises=premises.size(); i<npremises; i++)
    {
      size_t ii = (npremises-(i+1));
      std::stringstream nextRet;
      nextRet << "($eo_plist_cons " << getTimestampIndex(premises[ii]) << ret << ")";
      ret = nextRet.str();
    }
    d_cmds << " " << ret;
  }
  else
  {
    for (size_t i=0, npremises=premises.size(); i<npremises; i++)
    {
      d_cmds << " " << getTimestampIndex(premises[i]);
    }
  }
  d_cmds << "))" << std::endl;

  // ----------------------------------- old
  size_t nargs = 0;
  // prints as a definition
  std::stringstream stmp;
  for (size_t i = 0; i < args.size(); i++)
  {
    stmp << " ";
    printTerm(args[i], stmp);
    nargs++;
  }
  bool stdPremises = true;
  if (ainfo != nullptr)
  {
    Assert(ainfo->d_attrCons == Attr::PROOF_RULE);
    Expr tupleVal = ainfo->d_attrConsTerm;
    Assert(tupleVal.getNumChildren() == 3);
    Expr plCons;
    if (tupleVal[0].getKind() != Kind::ANY)
    {
      plCons = tupleVal[0];
    }
    bool isConcExplicit = tupleVal[2] == d_true;
    if (isConcExplicit)
    {
      if (proven.isNull())
      {
        return false;
      }
      stmp << " ";
      printTerm(proven, stmp);
      nargs++;
    }
    if (isPop)
    {
      std::vector<Expr> as = d_state.getCurrentAssumptions();
      stmp << " ";
      printTerm(as[0], stmp);
      nargs++;
    }
    if (!plCons.isNull())
    {
      stdPremises = false;
      std::vector<Expr> achildren;
      achildren.push_back(plCons);
      for (const Expr& e : premises)
      {
        std::stringstream tmp;
        tmp << "$eo_p_" << e;
        Expr dummy = d_state.mkSymbol(Kind::CONST, tmp.str(), d_boolType);
        achildren.push_back(dummy);
      }
      Expr ap;
      if (achildren.size() == 1)
      {
        // the nil terminator if applied to empty list
        AppInfo* aic = d_state.getAppInfo(plCons.getValue());
        Attr ck = aic->d_attrCons;
        if (ck == Attr::RIGHT_ASSOC_NIL || ck == Attr::LEFT_ASSOC_NIL)
        {
          ap = aic->d_attrConsTerm;
        }
        else
        {
          return false;
        }
      }
      else
      {
        ap = d_state.mkExpr(Kind::APPLY, achildren);
      }
      stmp << " ";
      printTerm(ap, stmp);
      nargs++;
    }
  }
  if (stdPremises)
  {
    for (size_t i = 0; i < premises.size(); i++)
    {
      stmp << " $eo_p_";
      printTerm(premises[i], stmp);
      nargs++;
    }
  }
  d_eoPfSteps << "(define $eo_p_" << name << " () ($smt_apply_" << nargs << " ";
  d_eoPfSteps << "\"$eor_" << rule << "\"";
  d_eoPfSteps << stmp.str();
  d_eoPfSteps << ")";
  // stmp << " :type Bool";
  d_eoPfSteps << ")" << std::endl;
  std::stringstream sname;
  if (!proven.isNull())
  {
    sname << "$eo_pc_" << name;
    d_eoPfSteps << "(define " << sname.str() << " () ";
    d_eoPfSteps << "($smt_apply_2 \"$eo_eq\" $eo_p_" << name << " ";
    printTerm(proven, d_eoPfSteps);
    d_eoPfSteps << "))" << std::endl;
  }
  else
  {
    sname << "$eo_p_" << name;
  }
  d_eoPfSteps << "(echo \"smt-meta-cmd (simplify " << sname.str() << ")\")"
              << std::endl;
  return false;
}

size_t DesugarProof::getTimestampIndex(const Expr& e)
{
  std::map<Expr, size_t>::iterator it = d_timestamp.find(e);
  Assert (it!=d_timestamp.end());
  Assert (it->second<d_currTimestamp);
  return d_currTimestamp - it->second;
}

void DesugarProof::bind(const std::string& name, const Expr& e)
{
  if (e.getKind()==Kind::PROOF)
  {
    d_timestamp[e[0]] = d_currTimestamp;
    d_currTimestamp++;
  }
}

void DesugarProof::printTerm(const Expr& e, std::ostream& os)
{
  d_desugar->printTerm(e, os);
}

}  // namespace ethos
