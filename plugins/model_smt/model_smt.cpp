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
  d_kindToEoPrefix[Kind::BOOLEAN] = "bool";
  d_kindToEoPrefix[Kind::NUMERAL] = "z";
  d_kindToEoPrefix[Kind::RATIONAL] = "q";
  d_kindToEoPrefix[Kind::STRING] = "str";
  d_kindToEoPrefix[Kind::BINARY] = "bin";
  d_kindToType[Kind::BOOLEAN] = "Bool";
  d_kindToType[Kind::NUMERAL] = "Int";
  d_kindToType[Kind::RATIONAL] = "Real";
  d_kindToType[Kind::STRING] = "String";
  d_kindToType[Kind::BINARY] = "Binary";
  // All SMT-LIB symbols that have monomorphic return go here.
  // We have a NUMERAL category that we assume can be associated to Int,
  // Similar for the other literals.
  // Note that we model *SMT-LIB* not *CPC* here.
  // builtin
  addHardCodeSym("=", {Kind::PARAM, Kind::PARAM});
  addHardCodeSym("ite", {Kind::BOOLEAN,Kind::PARAM, Kind::PARAM});
  // Booleans
  addConstFoldSym("and", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addConstFoldSym("or", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addConstFoldSym("xor", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addConstFoldSym("=>", {Kind::BOOLEAN, Kind::BOOLEAN}, Kind::BOOLEAN);
  addConstFoldSym("not", {Kind::BOOLEAN}, Kind::BOOLEAN);
  // arithmetic
  // use Kind::PARAM to stand for either Int or Real arithmetic (not mixed)
  // addConstFoldSym("Int", {}, Kind::TYPE);
  // addConstFoldSym("Real", {}, Kind::TYPE);
  addConstFoldSym("+", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  addConstFoldSym("-", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  addConstFoldSym("*", {Kind::PARAM, Kind::PARAM}, Kind::PARAM);
  // we expect "-" to be overloaded, we look for its desugared name and map it
  // back
  addConstFoldSym("$eoo_-.2", {Kind::PARAM}, Kind::PARAM);
  d_overloadRevert["$eoo_-.2"] = "-";
  addConstFoldSym("abs", {Kind::NUMERAL}, Kind::NUMERAL);
  addConstFoldSym(">=", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addConstFoldSym("<=", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addConstFoldSym(">", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addConstFoldSym("<", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addConstFoldSym("is_int", {Kind::RATIONAL}, Kind::BOOLEAN);
  addConstFoldSym("/", {Kind::RATIONAL, Kind::RATIONAL}, Kind::RATIONAL);
  addConstFoldSym("div", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addConstFoldSym("mod", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addConstFoldSym("to_int", {Kind::RATIONAL}, Kind::NUMERAL);
  addConstFoldSym("to_real", {Kind::NUMERAL}, Kind::RATIONAL);
  addTermReduceSym(
      "divisible", {Kind::NUMERAL, Kind::NUMERAL}, "(= (mod x2 x1) 0)");
  // strings
  // addConstFoldSym("String", {}, Kind::TYPE);
  addConstFoldSym("str.++", {Kind::STRING, Kind::STRING}, Kind::STRING);
  addConstFoldSym("str.len", {Kind::STRING}, Kind::NUMERAL);
  addConstFoldSym(
      "str.substr", {Kind::STRING, Kind::NUMERAL, Kind::NUMERAL}, Kind::STRING);
  addConstFoldSym("str.at", {Kind::STRING, Kind::NUMERAL}, Kind::STRING);
  addConstFoldSym("str.indexof",
                  {Kind::STRING, Kind::STRING, Kind::NUMERAL},
                  Kind::NUMERAL);
  addConstFoldSym(
      "str.replace", {Kind::STRING, Kind::STRING, Kind::STRING}, Kind::STRING);
  addConstFoldSym("str.replace_all",
                  {Kind::STRING, Kind::STRING, Kind::STRING},
                  Kind::STRING);
  addConstFoldSym("str.from_code", {Kind::NUMERAL}, Kind::STRING);
  addConstFoldSym("str.to_code", {Kind::STRING}, Kind::NUMERAL);
  addConstFoldSym("str.from_int", {Kind::NUMERAL}, Kind::STRING);
  addConstFoldSym("str.to_int", {Kind::STRING}, Kind::NUMERAL);
  addConstFoldSym("str.is_digit", {Kind::STRING}, Kind::BOOLEAN);
  addConstFoldSym("str.contains", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  addConstFoldSym("str.suffixof", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  addConstFoldSym("str.prefixof", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  addConstFoldSym("str.<=", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  addConstFoldSym("str.<", {Kind::STRING, Kind::STRING}, Kind::BOOLEAN);
  // bitvectors
  addLiteralBinReduceSym("bvand",
                         {Kind::BINARY, Kind::BINARY},
                         "x1",
                         "($smtx_binary_and x1 x2 x4)");
  addLiteralBinReduceSym(
      "bvor", {Kind::BINARY, Kind::BINARY}, "x1", "($smtx_binary_or x1 x2 x4)");
  addLiteralBinReduceSym("bvxor",
                         {Kind::BINARY, Kind::BINARY},
                         "x1",
                         "($smtx_binary_xor x1 x2 x4)");
  addTermReduceSym("bvsle", {Kind::BINARY, Kind::BINARY}, "(bvsge x2 x1)");
  addTermReduceSym("bvule", {Kind::BINARY, Kind::BINARY}, "(bvuge x2 x1)");
  addTermReduceSym("bvslt", {Kind::BINARY, Kind::BINARY}, "(bvsgt x2 x1)");
  addTermReduceSym("bvult", {Kind::BINARY, Kind::BINARY}, "(bvugt x2 x1)");
  addTermReduceSym(
      "nand", {Kind::BINARY, Kind::BINARY}, "(bvnot (bvand x1 x2))");
  addTermReduceSym("nor", {Kind::BINARY, Kind::BINARY}, "(bvnot (bvor x1 x2))");
  addTermReduceSym(
      "xnor", {Kind::BINARY, Kind::BINARY}, "(bvnot (bvxor x1 x2))");
  // Quantifiers
  for (size_t i = 0; i < 2; i++)
  {
    std::stringstream ssq;
    ssq << "($smtx_eval_quant x1 x2 $smt_builtin_z_zero $smt_builtin_"
        << (i == 0 ? "true" : "false") << ")";
    addReduceSym(
        i == 0 ? "exists" : "forall", {Kind::ANY, Kind::BOOLEAN}, ssq.str());
  }

  ///----- non standard extensions
  addConstFoldSym("^", {Kind::PARAM, Kind::PARAM}, Kind::BOOLEAN);
  addConstFoldSym("/_total", {Kind::PARAM, Kind::PARAM}, Kind::RATIONAL);
  addConstFoldSym("div_total", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addConstFoldSym("mod_total", {Kind::NUMERAL, Kind::NUMERAL}, Kind::NUMERAL);
  addConstFoldSym(
      "str.update", {Kind::STRING, Kind::NUMERAL, Kind::STRING}, Kind::STRING);
  addConstFoldSym("str.rev", {Kind::STRING}, Kind::STRING);
  addConstFoldSym("str.to_lower", {Kind::STRING}, Kind::STRING);
  addConstFoldSym("str.to_upper", {Kind::STRING}, Kind::STRING);
  // addConstFoldSym("int.ispow2", {Kind::NUMERAL, Kind::NUMERAL},
  // Kind::BOOLEAN); addConstFoldSym("int.log2", {Kind::NUMERAL, Kind::NUMERAL},
  // Kind::NUMERAL);
  addConstFoldSym("int.pow2", {Kind::NUMERAL}, Kind::NUMERAL);
  // TODO: more
  // BV
  // arith/BV conversions
  // addConstFoldSym("BitVec", {Kind::NUMERAL}, Kind::TYPE);
  // addConstFoldSym("int_to_bv", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BINARY);
  // addConstFoldSym("ubv_to_int", {Kind::BINARY}, Kind::NUMERAL);
  // addConstFoldSym("sbv_to_int", {Kind::BINARY}, Kind::NUMERAL);
}

ModelSmt::~ModelSmt() {}

void ModelSmt::addHardCodeSym(const std::string& sym,
                    const std::vector<Kind>& args)
{
  d_symHardCode[sym] = args;
}

void ModelSmt::addConstFoldSym(const std::string& sym,
                               const std::vector<Kind>& args,
                               Kind ret)
{
  d_symConstFold[sym] = std::pair<std::vector<Kind>, Kind>(args, ret);
}

void ModelSmt::addLiteralBinReduceSym(const std::string& sym,
                                      const std::vector<Kind>& args,
                                      const std::string& retWidth,
                                      const std::string& retNum)
{
  std::stringstream ssr;
  ssr << "($vsm_term ($sm_mk_binary " << retWidth << " " << retNum << "))";
  addLiteralReduceSym(sym, args, Kind::ANY, ssr.str());
}

void ModelSmt::addLiteralReduceSym(const std::string& sym,
                                   const std::vector<Kind>& args,
                                   Kind ret,
                                   const std::string& retTerm)
{
  d_symLitReduce[sym] =
      std::tuple<std::vector<Kind>, Kind, std::string>(args, ret, retTerm);
}

void ModelSmt::addTermReduceSym(const std::string& sym,
                                const std::vector<Kind>& args,
                                const std::string& retTerm)
{
  std::stringstream ssret;
  ssret << "($smtx_model_eval " << retTerm << ")";
  addReduceSym(sym, args, ssret.str());
}

void ModelSmt::addReduceSym(const std::string& sym,
                            const std::vector<Kind>& args,
                            const std::string& retTerm)
{
  d_symReduce[sym] = std::pair<std::vector<Kind>, std::string>(args, retTerm);
}

void ModelSmt::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  std::map<std::string, std::vector<Kind>>::iterator ith = d_symHardCode.find(name);
  if (ith!=d_symHardCode.end())
  {
    printModelEvalCall(name, ith->second);
    return;
  }
  // maybe a constant fold symbol
  std::map<std::string, std::pair<std::vector<Kind>, Kind>>::iterator it =
      d_symConstFold.find(name);
  if (it != d_symConstFold.end())
  {
    printModelEvalCall(name, it->second.first);
    printConstFold(name, it->second.first, it->second.second);
    return;
  }
  std::map<std::string,
           std::tuple<std::vector<Kind>, Kind, std::string>>::iterator its =
      d_symLitReduce.find(name);
  if (its != d_symLitReduce.end())
  {
    std::vector<Kind>& args = std::get<0>(its->second);
    printModelEvalCall(name, args);
    printLitReduce(
        name, args, std::get<1>(its->second), std::get<2>(its->second));
    return;
  }
  std::map<std::string, std::pair<std::vector<Kind>, std::string>>::iterator
      itst = d_symReduce.find(name);
  if (itst != d_symReduce.end())
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
  if (d_kindToEoPrefix.find(k) != d_kindToEoPrefix.end())
  {
    os << "($vsm_term ($sm_mk_" << d_kindToEoPrefix[k] << " " << term << "))";
  }
  else
  {
    os << term;
  }
}

void ModelSmt::printConstFold(const std::string& name,
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
    printAuxProgramCase(progName.str(),
                        instArgs,
                        fssret.str(),
                        paramCount,
                        progCases,
                        progParams);
  }
  printAuxProgram(progName.str(), args, progCases, progParams);
}

void ModelSmt::printAuxProgram(const std::string& name,
                               const std::vector<Kind>& args,
                               std::stringstream& progCases,
                               std::stringstream& progParams)
{
  std::stringstream progSig;
  progSig << "(";
  // make the default case as well
  progCases << "  ((" << name;
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
  progSig << ") $smt_Value";
  progCases << ") $vsm_not_value)" << std::endl;
  d_modelEvalProgs << "(program " << name << std::endl;
  d_modelEvalProgs << "  (" << progParams.str() << ")" << std::endl;
  d_modelEvalProgs << "  :signature " << progSig.str() << std::endl;
  d_modelEvalProgs << "  (" << std::endl;
  d_modelEvalProgs << progCases.str();
  d_modelEvalProgs << "  )" << std::endl << ")" << std::endl;
}

void ModelSmt::printAuxProgramCase(const std::string& name,
                                   const std::vector<Kind>& args,
                                   const std::string& ret,
                                   size_t& paramCount,
                                   std::ostream& progCases,
                                   std::ostream& progParams)
{
  progCases << "  ((" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    Kind ka = args[i - 1];
    paramCount++;
    if (paramCount > 1)
    {
      progParams << " ";
    }
    progCases << " ($vsm_term";
    if (ka == Kind::BINARY)
    {
      progCases << " ($sm_mk_binary x" << paramCount << " x" << (paramCount + 1)
                << "))";
      progParams << "(x" << paramCount << " $smt_builtin_Int)";
      progParams << " (x" << (paramCount + 1) << " $smt_builtin_Int)";
      paramCount++;
      continue;
    }
    Assert(d_kindToEoPrefix.find(ka) != d_kindToEoPrefix.end());
    progCases << " ($sm_mk_" << d_kindToEoPrefix[ka] << " x" << paramCount
              << "))";
    progParams << "(x" << paramCount << " $smt_builtin_" << d_kindToType[ka]
               << ")";
  }
  progCases << ") ";
  progCases << ret << ")" << std::endl;
}

void ModelSmt::printLitReduce(const std::string& name,
                              const std::vector<Kind>& args,
                              Kind ret,
                              const std::string& reduce)
{
  std::stringstream progName;
  std::stringstream progCases;
  std::stringstream progParams;
  size_t paramCount = 0;
  progName << "$smtx_model_eval_" << name;
  // print the term with the right type
  std::stringstream ssret;
  printTermInternal(ret, reduce, ssret);
  // then print it on cases
  printAuxProgramCase(
      progName.str(), args, ssret.str(), paramCount, progCases, progParams);
  printAuxProgram(progName.str(), args, progCases, progParams);
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
