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

void DesugarProof::output(std::ostream& out)
{
  // TODO
}

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
    Assert(!d_timestampScope.empty());
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
  // bool isAssume = tupleVal[1] == d_true;
  bool isConcExplicit = tupleVal[2] == d_true;

  d_cmds << "(define $eo_p_" << name << " () ($cmd_" << rule;
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
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
    for (size_t i = 0, npremises = premises.size(); i < npremises; i++)
    {
      size_t ii = (npremises - (i + 1));
      std::stringstream nextRet;
      nextRet << "($eo_plist_cons " << getTimestampIndex(premises[ii]) << ret
              << ")";
      ret = nextRet.str();
    }
    d_cmds << " " << ret;
  }
  else
  {
    for (size_t i = 0, npremises = premises.size(); i < npremises; i++)
    {
      d_cmds << " " << getTimestampIndex(premises[i]);
    }
  }
  d_cmds << "))" << std::endl;
  return false;
}

size_t DesugarProof::getTimestampIndex(const Expr& e)
{
  std::map<Expr, size_t>::iterator it = d_timestamp.find(e);
  Assert(it != d_timestamp.end());
  Assert(it->second < d_currTimestamp);
  return d_currTimestamp - it->second;
}

void DesugarProof::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() == Kind::PROOF)
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
