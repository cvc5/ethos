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

ModelSmt::ModelSmt(State& s) : StdPlugin(s)
{
  Expr typ = d_state.mkType();
  d_kindToEoPrefix[Kind::BOOLEAN] = "bool";
  d_kindToEoPrefix[Kind::NUMERAL] = "z";
  d_kindToEoPrefix[Kind::RATIONAL] = "q";
  d_kindToEoPrefix[Kind::STRING] = "str";
  d_kindToEoPrefix[Kind::BINARY] = "bin";
  d_kindToType[Kind::BOOLEAN] = "Bool";
  d_kindToType[Kind::NUMERAL] = "Int";
  d_kindToType[Kind::RATIONAL] = "Real";
  d_kindToType[Kind::STRING] = "String";
  // note BOOLEAN does not have a constructor as Bool is inlined
  d_kindToEoCons[Kind::NUMERAL] = "Numeral";
  d_kindToEoCons[Kind::RATIONAL] = "Rational";
  d_kindToEoCons[Kind::STRING] = "String";
  d_kindToEoCons[Kind::BINARY] = "Binary";
  // All SMT-LIB symbols that have monomorphic return go here.
  // We have a NUMERAL category that we assume can be associated to Int,
  // Similar for the other literals.
  // Note that we model *SMT-LIB* not *CPC* here.
  // builtin
  // addNormalSym("forall", {Kind::ANY, Kind::BOOLEAN}, Kind::BOOLEAN);
  // addNormalSym("exists", {Kind::ANY, Kind::BOOLEAN}, Kind::BOOLEAN);
  // Booleans
  addNormalSym("and", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addNormalSym("or", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addNormalSym("xor", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addNormalSym("=>", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addNormalSym("not", {Kind::BOOLEAN}, Kind::BOOLEAN);
  // arithmetic
  // use Kind::PARAM to stand for either Int or Real arithmetic (not mixed)
  // addNormalSym("Int", {}, Kind::TYPE);
  // addNormalSym("Real", {}, Kind::TYPE);
  addNormalSym("+", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  addNormalSym("-", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  addNormalSym("*", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  // we expect "-" to be overloaded, we look for its desugared name and map it
  // back
  addNormalSym("$eoo_-.2", {Kind::PARAM}, Kind::PARAM);
  d_overloadRevert["$eoo_-.2"] = "-";
  addNormalSym("abs", {Kind::NUMERAL}, Kind::NUMERAL);
  addNormalSym(">=", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addNormalSym("<=", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addNormalSym(">", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addNormalSym("<", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addNormalSym("is_int", {Kind::RATIONAL}, Kind::BOOLEAN);
  // NOTE: cannot handle indexed operators currently, as their value
  // cannot be dynamic in the encoding.
  // addNormalSym("divisible", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BOOLEAN);
  addNormalSym("/", {Kind::RATIONAL, Kind::RATIONAL}, Kind::RATIONAL);
  addNormalSym("div", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addNormalSym("mod", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addNormalSym("to_int", {Kind::RATIONAL}, Kind::NUMERAL);
  addNormalSym("to_real", {Kind::NUMERAL}, Kind::RATIONAL);
  // strings
  // addNormalSym("String", {}, Kind::TYPE);
  addNormalSym("str.++", {Kind::STRING, Kind::STRING}, Kind::STRING);
  addNormalSym("str.len", {Kind::STRING}, Kind::NUMERAL);
  addNormalSym(
      "str.substr", {Kind::STRING, Kind::NUMERAL, Kind::NUMERAL}, Kind::STRING);
  addNormalSym("str.at", {Kind::STRING, Kind::NUMERAL}, Kind::STRING);
  addNormalSym("str.indexof",
               {Kind::STRING, Kind::STRING, Kind::NUMERAL},
               Kind::NUMERAL);
  addNormalSym(
      "str.replace", {Kind::STRING, Kind::STRING, Kind::STRING}, Kind::STRING);
  addNormalSym("str.replace_all",
               {Kind::STRING, Kind::STRING, Kind::STRING},
               Kind::STRING);
  addNormalSym("str.from_code", {Kind::NUMERAL}, Kind::STRING);
  addNormalSym("str.to_code", {Kind::STRING}, Kind::NUMERAL);
  addNormalSym("str.from_int", {Kind::NUMERAL}, Kind::STRING);
  addNormalSym("str.to_int", {Kind::STRING}, Kind::NUMERAL);
  addNormalSym("str.is_digit", {Kind::STRING}, Kind::BOOLEAN);
  addNormalSym("str.contains", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  addNormalSym("str.suffixof", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  addNormalSym("str.prefixof", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  addNormalSym("str.<=", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  addNormalSym("str.<", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);

  ///----- non standard extensions
  addNormalSym("^", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addNormalSym("/_total", {Kind::PARAM, Kind::PARAM}, Kind::RATIONAL);
  addNormalSym("div_total", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addNormalSym("mod_total", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addNormalSym(
      "str.update", {Kind::STRING, Kind::NUMERAL, Kind::STRING}, Kind::STRING);
  addNormalSym("str.rev", {Kind::STRING}, Kind::STRING);
  addNormalSym("str.to_lower", {Kind::STRING}, Kind::STRING);
  addNormalSym("str.to_upper", {Kind::STRING}, Kind::STRING);
  // addNormalSym("int.ispow2", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BOOLEAN);
  // addNormalSym("int.log2", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addNormalSym("int.pow2", {Kind::NUMERAL}, Kind::NUMERAL);
  // TODO: more
  // BV
  // arith/BV conversions
  // addNormalSym("BitVec", {Kind::NUMERAL}, Kind::TYPE);
  // addNormalSym("int_to_bv", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BINARY);
  // addNormalSym("ubv_to_int", {Kind::BINARY}, Kind::NUMERAL);
  // addNormalSym("sbv_to_int", {Kind::BINARY}, Kind::NUMERAL);
}

ModelSmt::~ModelSmt() {}

void ModelSmt::addNormalSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            Kind ret)
{
  d_symNormal[sym] = std::pair<std::vector<Kind>, Kind>(args, ret);
}

void ModelSmt::addReduceSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            Kind ret,
                            const std::string& retTerm)
{
  d_symReduce[sym] =
      std::tuple<std::vector<Kind>, Kind, std::string>(args, ret, retTerm);
}

void ModelSmt::addTermReduceSym(const std::string& sym,
                                const std::vector<Kind>& args,
                                const std::string& retTerm)
{
  d_symTermReduce[sym] =
      std::pair<std::vector<Kind>, std::string>(args, retTerm);
}

void ModelSmt::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  // maybe a normal symbol
  std::map<std::string, std::pair<std::vector<Kind>, Kind>>::iterator it =
      d_symNormal.find(name);
  if (it != d_symNormal.end())
  {
    printModelEvalCall(name, it->second.first);
    printNormal(name, it->second.first, it->second.second);
    return;
  }
  std::map<std::string,
           std::tuple<std::vector<Kind>, Kind, std::string>>::iterator its =
      d_symReduce.find(name);
  if (its != d_symReduce.end())
  {
    std::vector<Kind>& args = std::get<0>(its->second);
    printModelEvalCall(name, args);
    printReduce(name, args, std::get<1>(its->second), std::get<2>(its->second));
    return;
  }
  std::map<std::string, std::pair<std::vector<Kind>, std::string>>::iterator
      itst = d_symTermReduce.find(name);
  if (itst != d_symTermReduce.end())
  {
    printModelEvalCallBase(name, itst->second.first, itst->second.second);
    return;
  }
}

void ModelSmt::printType(const std::string& name, const std::vector<Kind>& args)
{
}

void ModelSmt::printModelEvalCallBase(const std::string& name,
                                      const std::vector<Kind>& args,
                                      const std::string& ret)
{
  d_eval << "  (($smtx_model_eval (" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    d_eval << " x" << i;
  }
  d_eval << ")) " << ret << ")" << std::endl;
  ;
}
void ModelSmt::printModelEvalCall(const std::string& name,
                                  const std::vector<Kind>& args)
{
  std::stringstream callArgs;
  callArgs << "($smtx_model_eval_" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    callArgs << " ($smtx_model_eval x" << i << ")";
  }
  callArgs << ")";
  printModelEvalCallBase(name, args, callArgs.str());
}

void ModelSmt::printTermInternal(Kind k,
                                 const std::string& term,
                                 std::ostream& os)
{
  Assert(d_kindToEoPrefix.find(k) != d_kindToEoPrefix.end());
  os << "($vsm_term ($sm_mk_" << d_kindToEoPrefix[k] << " " << term << "))";
}

void ModelSmt::printNormal(const std::string& name,
                           const std::vector<Kind>& args,
                           Kind kret)
{
  bool isOverloadArith = (args.size() > 0 && args[0] == Kind::PARAM);
  std::vector<Kind> argSchemas;
  if (isOverloadArith)
  {
    // will print conditions in two ways
    argSchemas.push_back(Kind::NUMERAL);
    argSchemas.push_back(Kind::RATIONAL);
  }
  else
  {
    argSchemas.push_back(Kind::NONE);
  }
  std::stringstream progName;
  progName << "$smtx_model_eval_" << name;
  std::stringstream progCases;
  std::stringstream progParams;
  size_t paramCount = 0;
  for (Kind kas : argSchemas)
  {
    // instantiate the arguments for the current schema and prepare the
    // argument list for the return term.
    std::vector<Kind> instArgs;
    std::stringstream retArgs;
    size_t tmpParamCount = paramCount;
    for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
    {
      Kind ka = args[i - 1];
      instArgs.push_back(ka == Kind::PARAM ? kas : ka);
      tmpParamCount++;
      retArgs << " x" << tmpParamCount;
    }
    // print the return term
    Kind kr = kret == Kind::PARAM ? kas : kret;
    std::stringstream ssret;
    ssret << "($smt_apply_" << args.size() << " \"";
    std::map<std::string, std::string>::iterator ito =
        d_overloadRevert.find(name);
    if (ito != d_overloadRevert.end())
    {
      // e.g. in spite of having name $eoo_-.2, we use "-" as the invocation.
      ssret << ito->second;
    }
    else
    {
      ssret << name;
    }
    ssret << "\"" << retArgs.str() << ")";
    // print the term with the right type
    std::stringstream fssret;
    printTermInternal(kr, ssret.str(), fssret);
    // then print it on cases
    printInternal(progName.str(),
                  instArgs,
                  fssret.str(),
                  paramCount,
                  progCases,
                  progParams);
  }
  std::stringstream progSig;
  progSig << "(";
  // make the default case as well
  progCases << "  ((" << progName.str();
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    if (i > 0)
    {
      progSig << " ";
    }
    progSig << "$smt_Value";
    progCases << " t" << (i + 1);
    progParams << " (t" << (i + 1) << " $smt_Value)";
  }
  progSig << ") $smt_Value" << std::endl;
  progCases << ") $vsm_not_value)" << std::endl;
  d_modelEvalProgs << "(program " << progName.str() << std::endl;
  d_modelEvalProgs << "  (" << progParams.str() << ")" << std::endl;
  d_modelEvalProgs << "  :signature " << progSig.str() << std::endl;
  d_modelEvalProgs << "  (" << std::endl;
  d_modelEvalProgs << progCases.str();
  d_modelEvalProgs << "  )" << std::endl << ")" << std::endl;
}

/*
  if (name == "forall" || name == "exists")
  {
    // does not "pre-rewrite" the body
    bool isExists = (name == "exists");
    d_eval << "($smtx_eval_quant x1 x2 $smt_builtin_z_zero ";
    d_eval << "$smt_builtin_" << (isExists ? "true" : "false") << "))";
    return;
  }
  */
void ModelSmt::printInternal(const std::string& name,
                             const std::vector<Kind>& args,
                             const std::string& ret,
                             size_t& paramCount,
                             std::ostream& progCases,
                             std::ostream& progParams)
{
  progCases << "  ((" << name;
  std::stringstream retArgs;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    Kind ka = args[i - 1];
    paramCount++;
    if (paramCount > 1)
    {
      progParams << " ";
    }
    progCases << " ($vsm_term ($sm_mk_" << d_kindToEoPrefix[ka] << " x"
              << paramCount << "))";
    retArgs << " x" << paramCount;
    progParams << "(x" << paramCount << " $smt_builtin_" << d_kindToType[ka]
               << ")";
  }
  progCases << ") ";
  progCases << ret << ")" << std::endl;
}

void ModelSmt::printSmtx(const std::string& name,
                         const std::vector<Kind>& args,
                         Kind ret,
                         const std::string& smtxName)
{
  std::stringstream scall;
  scall << "($smtx_" << smtxName;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    scall << " x" << i;
  }
  scall << ")";
  printReduce(name, args, ret, scall.str());
}

void ModelSmt::printReduce(const std::string& name,
                           const std::vector<Kind>& args,
                           Kind ret,
                           const std::string& reduce)
{
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

  // note that the deep embedding is *not* re-incorporated into
  // the final input to smt-meta.

  // now, go back and compile *.eo for the proof rules
  std::stringstream ssis;
  ssis << s_plugin_path << "plugins/model_smt/model_smt.eo";
  std::ifstream ins(ssis.str());
  std::ostringstream sss;
  sss << ins.rdbuf();
  std::string finalSmt = sss.str();
  replace(finalSmt, "$EO_TYPE_ENUM_CASES$", d_typeEnum.str());
  replace(finalSmt, "$EO_IS_VALUE_CASES$", d_isValue.str());
  replace(finalSmt, "$EO_IS_TYPE_CASES$", d_isType.str());
  replace(finalSmt, "$EO_EVAL_CASES$", d_customEval.str());
  replace(finalSmt, "$SMT_MODEL_LOOKUP_PREDICATE_CASES$", d_constPred.str());
  // plug in the evaluation cases handled by this plugin
  replace(finalSmt, "$SMT_EVAL_CASES$", d_eval.str());
  replace(finalSmt, "$SMT_EVAL_PROGS$", d_modelEvalProgs.str());

  std::stringstream ssoe;
  ssoe << s_plugin_path << "plugins/model_smt/model_smt_gen.eo";
  // std::cout << "Write smt-model    " << finalSmt.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << finalSmt;
}

}  // namespace ethos
