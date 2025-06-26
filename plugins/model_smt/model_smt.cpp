/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "model_smt.h"

#include <fstream>
#include <sstream>
#include <string>

#include "state.h"

namespace ethos {

// std::string s_ds_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
std::string s_smodel_path = "/home/andrew/ethos/";

ModelSmt::ModelSmt(State& s) : d_state(s), d_tc(s.getTypeChecker())
{
  // All SMT-LIB symbols that have monomorphic return go here.
  // We have a NUMERAL category that we assume can be associated to Int,
  // Similar for the other literals.
  // Note that we model *SMT-LIB* not *CPC* here.
  // builtin
  // use ANY to stand for any literal type
  addSmtLibSym("=", {Kind::ANY, Kind::ANY}, Kind::BOOLEAN);
  // Booleans
  addSmtLibSym("and", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addSmtLibSym("or", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addSmtLibSym("xor", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addSmtLibSym("not", {Kind::BOOLEAN}, Kind::BOOLEAN);
  // arithmetic
  // use Kind::PARAM to stand for either Int or Real arithmetic (not mixed)
  addSmtLibSym("Int", {}, Kind::TYPE);
  addSmtLibSym("Real", {}, Kind::TYPE);
  addSmtLibSym("+", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  addSmtLibSym("-", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  addSmtLibSym("*", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  addSmtLibSym("abs", {Kind::PARAM}, Kind::PARAM);
  addSmtLibSym(">=", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addSmtLibSym("<=", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addSmtLibSym(">", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addSmtLibSym("<", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addSmtLibSym("is_int", {Kind::RATIONAL}, Kind::BOOLEAN);
  addSmtLibSym("divisible", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BOOLEAN);
  addSmtLibSym("/", {Kind::RATIONAL, Kind::RATIONAL}, Kind::RATIONAL);
  addSmtLibSym("div", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addSmtLibSym("mod", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addSmtLibSym("to_int", {Kind::RATIONAL}, Kind::NUMERAL);
  addSmtLibSym("to_real", {Kind::NUMERAL}, Kind::RATIONAL);
  // strings
  addSmtLibSym("String", {}, Kind::TYPE);
  addSmtLibSym("str.++", {Kind::STRING, Kind::STRING}, Kind::STRING);
  addSmtLibSym("str.substr", {Kind::STRING, Kind::NUMERAL, Kind::NUMERAL}, Kind::STRING);
  addSmtLibSym("str.substr", {Kind::STRING}, Kind::NUMERAL);
  addSmtLibSym("str.indexof", {Kind::STRING, Kind::STRING, Kind::NUMERAL}, Kind::NUMERAL);
  addSmtLibSym("str.to_lower", {Kind::STRING}, Kind::STRING);
  addSmtLibSym("str.to_upper", {Kind::STRING}, Kind::STRING);
  addSmtLibSym("str.from_code", {Kind::NUMERAL}, Kind::STRING);
  addSmtLibSym("str.to_code", {Kind::STRING}, Kind::NUMERAL);
  // BV
  // arith/BV conversions
  addSmtLibSym("BitVec", {Kind::NUMERAL}, Kind::TYPE);
  addSmtLibSym("int_to_bv", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BINARY);
  addSmtLibSym("ubv_to_int", {Kind::BINARY}, Kind::NUMERAL);
  addSmtLibSym("sbv_to_int", {Kind::BINARY}, Kind::NUMERAL);
}

ModelSmt::~ModelSmt() {}


void ModelSmt::addSmtLibSym(const std::string& sym, const std::vector<Kind>& args, Kind ret)
{
  d_smtLibSyms[sym] = std::pair<std::vector<Kind>, Kind>(args, ret);
}

void ModelSmt::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  std::map<std::string, std::pair<std::vector<Kind>, Kind>>::iterator it = d_smtLibSyms.find(name);
  if (it==d_smtLibSyms.end())
  {
    return;
  }
  std::vector<Kind>& args = it->second.first;
  Kind ret = it->second.second;
  if (ret==Kind::TYPE)
  {
    printSmtType(name, args);
  }
  else
  {
    printSmtTerm(name, args, ret);
  }
}

void ModelSmt::printSmtType(const std::string& name, std::vector<Kind>& args)
{
}

void ModelSmt::printSmtTerm(const std::string& name, std::vector<Kind>& args, Kind ret)
{
}

void ModelSmt::printTerm(const Expr& e, std::ostream& os)
{
  os << e;
}

void ModelSmt::printParamList(const std::vector<Expr>& vars,
                             std::ostream& os,
                             std::vector<Expr>& params,
                             bool useImplicit)
{
  std::map<Expr, bool> visited;
  bool firstParam = true;
  printParamList(vars, os, params, useImplicit, visited, firstParam);
}

void ModelSmt::printParamList(const std::vector<Expr>& vars,
                             std::ostream& os,
                             std::vector<Expr>& params,
                             bool useImplicit,
                             std::map<Expr, bool>& visited,
                             bool& firstParam,
                             bool isOpaque)
{
  std::map<Expr, bool>::iterator itv;
  std::vector<Expr> toVisit(vars.begin(), vars.end());
  Expr cur;
  while (!toVisit.empty())
  {
    cur = toVisit.back();
    Assert(cur.getKind() == Kind::PARAM);
    itv = visited.find(cur);
    if (itv != visited.end() && itv->second)
    {
      toVisit.pop_back();
      continue;
    }
    Expr tcur = d_tc.getType(cur);
    if (itv == visited.end())
    {
      visited[cur] = false;
      // ensure its type has been printed
      Assert(!tcur.isNull());
      std::vector<Expr> tvars = Expr::getVariables(tcur);
      toVisit.insert(toVisit.end(), tvars.begin(), tvars.end());
      continue;
    }
    else if (!itv->second)
    {
      Assert(!itv->second);
      visited[cur] = true;
      if (firstParam)
      {
        firstParam = false;
      }
      else
      {
        os << " ";
      }
      os << "(" << cur << " ";
      printTerm(tcur, os);
      if (std::find(vars.begin(), vars.end(), cur) == vars.end())
      {
        if (useImplicit)
        {
          os << " :implicit";
        }
      }
      else if (isOpaque)
      {
        os << " :opaque";
      }
      os << ")";
      toVisit.pop_back();
      params.push_back(cur);
    }
  }
}

void ModelSmt::finalize()
{
  // now we can finish the definitions
  std::vector<Expr> paramsTmp;
  printParamList(d_evalParams, d_evalParam, paramsTmp, false);
  printParamList(d_typeEnumParams, d_evalParam, paramsTmp, false);

  auto replace = [](std::string& txt,
                    const std::string& tag,
                    const std::string& replacement) {
    auto pos = txt.find(tag);
    if (pos != std::string::npos)
    {
      txt.replace(pos, tag.length(), replacement);
    }
  };

  // now, go back and compile *.eo for the proof rules
  std::stringstream ssie;
  ssie << s_smodel_path << "plugins/model_smt/model_smt.eo";
  std::ifstream ine(ssie.str());
  std::ostringstream sse;
  sse << ine.rdbuf();
  std::string finalEo = sse.str();

  replace(finalEo, "$SMT_EVAL_PARAM$", d_evalParam.str());
  replace(finalEo, "$SMT_EVAL_NGROUND_DEFS$", d_evalNGround.str());
  replace(finalEo, "$SMT_EVAL_CASES$", d_eval.str());
  replace(finalEo, "$SMT_TYPE_ENUM_PARAM$", d_typeEnumParam.str());
  replace(finalEo, "$SMT_TYPE_ENUM_NGROUND_DEFS$", d_typeEnumNGround.str());
  replace(finalEo, "$SMT_TYPE_ENUM_CASES$", d_typeEnum.str());

  std::stringstream ssoe;
  ssoe << s_smodel_path << "plugins/model_smt/model_smt_gen.eo";
  std::cout << "Write smt-model    " << ssoe.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << finalEo;


}

}  // namespace ethos
