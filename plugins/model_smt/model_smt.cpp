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

//std::string s_smodel_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
std::string s_smodel_path = "/home/andrew/ethos/";

ModelSmt::ModelSmt(State& s) : d_state(s), d_tc(s.getTypeChecker())
{
  Expr typ = d_state.mkType();
  d_kindToType[Kind::BOOLEAN] = d_state.mkBoolType();
  d_kindToType[Kind::NUMERAL] =
      d_state.mkSymbol(Kind::CONST, "$eo_Numeral", typ);
  d_kindToType[Kind::RATIONAL] =
      d_state.mkSymbol(Kind::CONST, "$eo_Rational", typ);
  d_kindToType[Kind::STRING] = d_state.mkSymbol(Kind::CONST, "$eo_String", typ);
  d_kindToType[Kind::BINARY] = d_state.mkSymbol(Kind::CONST, "$eo_BINARY", typ);
  d_kindToType[Kind::ANY] = d_state.mkSymbol(Kind::CONST, "Any", typ);
  d_kindToEoPrefix[Kind::BOOLEAN] = "bool";
  d_kindToEoPrefix[Kind::NUMERAL] = "z";
  d_kindToEoPrefix[Kind::RATIONAL] = "q";
  d_kindToEoPrefix[Kind::STRING] = "str";
  d_kindToEoPrefix[Kind::BINARY] = "bin";
  // All SMT-LIB symbols that have monomorphic return go here.
  // We have a NUMERAL category that we assume can be associated to Int,
  // Similar for the other literals.
  // Note that we model *SMT-LIB* not *CPC* here.
  // builtin
  addSmtLibSym("forall", {Kind::ANY, Kind::BOOLEAN}, Kind::BOOLEAN);
  addSmtLibSym("exists", {Kind::ANY, Kind::BOOLEAN}, Kind::BOOLEAN);
  addSmtLibSym("=", {Kind::ANY, Kind::ANY}, Kind::BOOLEAN);
  addSmtLibSym("ite", {Kind::BOOLEAN, Kind::ANY, Kind::ANY}, Kind::ANY);
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
  // we expect "-" to be overloaded, we look for its desugared name and map it
  // back
  // addSmtLibSym("$eoo_-.2", {Kind::PARAM}, Kind::PARAM);
  // d_overloadRevert["$eoo_-.2"] = "-";
  // addSmtLibSym("abs", {Kind::PARAM}, Kind::PARAM);
  addSmtLibSym(">=", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addSmtLibSym("<=", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addSmtLibSym(">", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addSmtLibSym("<", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addSmtLibSym("is_int", {Kind::RATIONAL}, Kind::BOOLEAN);
  // NOTE: cannot handle indexed operators currently, as their value
  // cannot be dynamic in the encoding.
  //addSmtLibSym("divisible", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BOOLEAN);
  addSmtLibSym("/", {Kind::RATIONAL, Kind::RATIONAL}, Kind::RATIONAL);
  addSmtLibSym("div", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addSmtLibSym("mod", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addSmtLibSym("to_int", {Kind::RATIONAL}, Kind::NUMERAL);
  addSmtLibSym("to_real", {Kind::NUMERAL}, Kind::RATIONAL);
  // strings
  addSmtLibSym("String", {}, Kind::TYPE);
  addSmtLibSym("str.++", {Kind::STRING, Kind::STRING}, Kind::STRING);
  addSmtLibSym(
      "str.substr", {Kind::STRING, Kind::NUMERAL, Kind::NUMERAL}, Kind::STRING);
  addSmtLibSym(
      "str.substr", {Kind::STRING, Kind::NUMERAL, Kind::NUMERAL}, Kind::STRING);
  addSmtLibSym("str.indexof",
               {Kind::STRING, Kind::STRING, Kind::NUMERAL},
               Kind::NUMERAL);
  addSmtLibSym("str.to_lower", {Kind::STRING}, Kind::STRING);
  addSmtLibSym("str.to_upper", {Kind::STRING}, Kind::STRING);
  addSmtLibSym("str.from_code", {Kind::NUMERAL}, Kind::STRING);
  addSmtLibSym("str.to_code", {Kind::STRING}, Kind::NUMERAL);
  // TODO: more
  // BV
  // arith/BV conversions
  // addSmtLibSym("BitVec", {Kind::NUMERAL}, Kind::TYPE);
  // addSmtLibSym("int_to_bv", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BINARY);
  // addSmtLibSym("ubv_to_int", {Kind::BINARY}, Kind::NUMERAL);
  // addSmtLibSym("sbv_to_int", {Kind::BINARY}, Kind::NUMERAL);
}

ModelSmt::~ModelSmt() {}

void ModelSmt::addSmtLibSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            Kind ret)
{
  d_smtLibSyms[sym] = std::pair<std::vector<Kind>, Kind>(args, ret);
}

void ModelSmt::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  std::map<std::string, std::pair<std::vector<Kind>, Kind>>::iterator it =
      d_smtLibSyms.find(name);
  if (it == d_smtLibSyms.end())
  {
    return;
  }
  std::vector<Kind>& args = it->second.first;
  Kind ret = it->second.second;
  if (ret == Kind::TYPE)
  {
    printSmtType(name, args);
  }
  else
  {
    printSmtTerm(name, args, ret);
  }
}

void ModelSmt::printSmtType(const std::string& name, std::vector<Kind>& args) {}

void ModelSmt::printSmtTerm(const std::string& name,
                            std::vector<Kind>& args,
                            Kind kret)
{
  d_eval << "  (($smt_model_eval (" << name;
  // special cases
  if (name == "ite")
  {
    d_eval << " x1 x2 x3)) ";
    d_eval << "(eo::ite ($smt_model_eval x1) ($smt_model_eval x2) "
              "($smt_model_eval x3)))";
    d_eval << std::endl;
    return;
  }
  bool isOverloadArith = (args.size() > 0 && args[0] == Kind::PARAM);
  std::stringstream preApp;
  std::stringstream preAppEnd;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    preApp << "    (eo::define ((e" << i << " ($smt_model_eval x" << i << ")))" << std::endl;
    preAppEnd << ")";
  }
  if (name == "=")
  {
    // Note that we do not insist on converting to SMT-LIB literals here
    // We rely on SMT-LIB equality, guarding by an $smt_is_value predicate.
    d_eval << " x1 x2))" << std::endl;
    d_eval << preApp.str();
    d_eval << "      ($smt_eval_= ($smt_typeof x1) e1 e2 (= x1 x2))" << preAppEnd.str() << ")";
    d_eval << std::endl;
  }
  else if (name == "forall" || name == "exists")
  {
    // does not "pre-rewrite" the body
    bool isExists = (name == "exists");
    d_eval << " x1 x2)) ($smt_eval_quant x1 x2 0 " << isExists << "))";
  }
  else if (isOverloadArith)
  {
    // overloaded arithmetic
    if (args.size() == 2)
    {
      Assert(args[0] == Kind::PARAM && args[1] == Kind::PARAM);
      d_eval << " x1 x2)) ($smt_eval_o_arith";
      if (kret == Kind::BOOLEAN)
      {
        d_eval << "_pred";
      }
      d_eval << " \"" << name << "\" x1 x2 (" << name << " x1 x2)))" << std::endl;
    }
    else if (args.size() == 1)
    {
      d_eval << " x1)) ($smt_eval_o_arith_unary ";
      d_eval << " \"" << name << "\" x1 (" << name << " x1)))" << std::endl;
    }
    else
    {
      // otherwise not handled
      EO_FATAL() << "Cannot handle given overloaded arith type schema";
    }
    return;
  }
  else
  {
    std::stringstream appArgs;
    appArgs << " \"" << name << "\"";
    for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
    {
      d_eval << " x" << i;
      Kind ka = args[i - 1];
      // use guarded version
      appArgs << " ($smt_from_eo_";
      if (d_kindToEoPrefix.find(ka) != d_kindToEoPrefix.end())
      {
        appArgs << d_kindToEoPrefix[ka];
      }
      else
      {
        EO_FATAL() << "Unknown argument kind: " << ka;
      }
      appArgs << " e" << i << ")";
    }
    std::stringstream ssretBase;
    if (args.empty() || args.size() > 3)
    {
      EO_FATAL() << "Unhandled arity " << args.size() << " for " << name;
    }
    d_eval << ")) " << preApp.str() << "      ($smt_to_eo_";
    if (d_kindToEoPrefix.find(kret) != d_kindToEoPrefix.end())
    {
      d_eval << d_kindToEoPrefix[kret];
    }
    else
    {
      EO_FATAL() << "Unknown return kind: " << kret;
    }
    d_eval << " ($smt_apply_" << args.size() << appArgs.str() << ")))"
           << preAppEnd.str() << std::endl;
  }
}

void ModelSmt::finalize()
{
  auto replace = [](std::string& txt,
                    const std::string& tag,
                    const std::string& replacement) {
    auto pos = txt.find(tag);
    if (pos != std::string::npos)
    {
      txt.replace(pos, tag.length(), replacement);
    }
  };
  // read the preamble
  std::stringstream ssiep;
  ssiep << s_smodel_path << "plugins/model_smt/model_eo_preamble.eo";
  std::ifstream inep(ssiep.str());
  std::ostringstream ssep;
  ssep << inep.rdbuf();
  std::string finalEoPremable = ssep.str();

  std::stringstream ssie;
  ssie << s_smodel_path << "plugins/model_smt/model_eo.eo";
  std::ifstream ine(ssie.str());
  std::ostringstream sse;
  sse << ine.rdbuf();
  std::string finalEo = sse.str();
  replace(finalEo, "$EO_IS_TYPE_CASES$", d_typeEnum.str());
  replace(finalEo, "$EO_TYPE_ENUM_CASES$", d_isValue.str());
  replace(finalEo, "$EO_CONST_PREDICATE_CASES$", d_constPred.str());
  replace(finalEo, "$EO_EVAL_CASES$", d_customEval.str());

  // now, go back and compile *.eo for the proof rules
  std::stringstream ssis;
  ssis << s_smodel_path << "plugins/model_smt/model_smt.eo";
  std::ifstream ins(ssis.str());
  std::ostringstream sss;
  sss << ins.rdbuf();
  std::string finalSmt = sss.str();
  replace(finalSmt, "$SMT_EVAL_CASES$", d_eval.str());

  std::stringstream ssoe;
  ssoe << s_smodel_path << "plugins/model_smt/model_smt_gen.eo";
  //std::cout << "Write smt-model    " << finalSmt.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << finalEo; // the final user defined signature, as a preamble
  oute << finalSmt;
}

}  // namespace ethos
