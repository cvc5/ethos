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

#include "../smt_meta/smt_meta_reduce.h"
#include "state.h"

namespace ethos {

std::string dtKindToString(DtKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case DtKind::EUNOIA_TERM: ss << "EUNOIA_TERM"; break;
    case DtKind::SMT_TERM: ss << "SMT_TERM"; break;
    case DtKind::SMT_TYPE: ss << "SMT_TYPE"; break;
    case DtKind::SMT_VALUE: ss << "SMT_VALUE"; break;
    default: ss << "?DtKind"; break;
  }
  return ss.str();
}

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
  addSmtLibSym("forall", {Kind::ANY, Kind::BOOLEAN}, Kind::BOOLEAN);
  addSmtLibSym("exists", {Kind::ANY, Kind::BOOLEAN}, Kind::BOOLEAN);
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
  // addSmtLibSym("divisible", {Kind::NUMERAL, Kind::NUMERAL}, Kind::BOOLEAN);
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
  d_declSeen.insert(e);
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
  std::stringstream callApp;
  callApp << "(" << name;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    callApp << " x" << i;
  }
  callApp << ")";
  // This needs to be here, this is the user include of a standard
  // template
  d_eval << "  (($smtx_model_eval " << callApp.str() << ")";
  bool isOverloadArith = (args.size() > 0 && args[0] == Kind::PARAM);
  if (name == "forall" || name == "exists")
  {
    // does not "pre-rewrite" the body
    bool isExists = (name == "exists");
    d_eval << "($smtx_eval_quant x1 x2 0 " << isExists << "))";
    return;
  }
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
    progCases << "  ((" << progName.str();
    std::stringstream retArgs;
    for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
    {
      Kind ka = args[i - 1];
      if (ka == Kind::PARAM)
      {
        Assert(kas != Kind::NONE);
        ka = kas;
      }
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
    Kind kr = kret;
    if (kr == Kind::PARAM)
    {
      Assert(kas != Kind::NONE);
      kr = kas;
    }
    Assert(d_kindToEoPrefix.find(kr) != d_kindToEoPrefix.end())
        << "Could not find kind ret " << kr;
    progCases << "($vsm_term ($sm_mk_" << d_kindToEoPrefix[kr];
    progCases << " ($smt_apply_" << args.size() << " \"" << name << "\"";
    progCases << retArgs.str() << "))))" << std::endl;
  }
  std::stringstream progSig;
  progSig << "(";
  // make the default case as well
  progCases << "  ((" << progName.str();
  d_eval << " (" << progName.str();
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    if (i > 0)
    {
      progSig << " ";
    }
    d_eval << " ($smtx_model_eval x" << (i + 1) << ")";
    progSig << "$smt_Value";
    progCases << " t" << (i + 1);
    progParams << " (t" << (i + 1) << " $smt_Value)";
  }
  progSig << ") $smt_Value" << std::endl;
  d_eval << "))" << std::endl;
  progCases << ") $vsm_not_value)" << std::endl;
  d_modelEvalProgs << "(program " << progName.str() << std::endl;
  d_modelEvalProgs << "  (" << progParams.str() << ")" << std::endl;
  d_modelEvalProgs << "  :signature " << progSig.str() << std::endl;
  d_modelEvalProgs << "  (" << std::endl;
  d_modelEvalProgs << progCases.str();
  d_modelEvalProgs << "  )" << std::endl << ")" << std::endl;
}

void ModelSmt::printEmbType(const Expr& e, std::ostream& os)
{
  if (!SmtMetaReduce::printMetaType(e, os))
  {
    Assert(false) << "Failed to get meta-type for " << e;
    os << e;
  }
}

void ModelSmt::finalizeDecl(const Expr& e)
{
  // first, determine which datatype (if any) this belongs to
  std::stringstream ss;
  ss << e;
  std::string sname = ss.str();
  std::stringstream* out = nullptr;
  std::stringstream cname;
  // get the meta-kind based on its name
  std::string cnamek;
  TermContextKind tk = SmtMetaReduce::getMetaKind(d_state, e, cnamek);
  if (tk == TermContextKind::EUNOIA)
  {
    cname << "eo." << cnamek;
    out = &d_embedEoTermDt;
  }
  else if (tk == TermContextKind::SMT_TYPE)
  {
    cname << "tsm." << cnamek;
    out = &d_embedTypeDt;
  }
  else if (tk == TermContextKind::SMT)
  {
    cname << "sm." << cnamek;
    out = &d_embedTermDt;
  }
  else if (tk == TermContextKind::SMT_VALUE)
  {
    cname << "vsm." << cnamek;
    out = &d_embedValueDt;
  }
  if (out == nullptr)
  {
    std::cout << "Do not include " << e << std::endl;
    return;
  }
  std::cout << "Include " << e << std::endl;
  bool isEmbedCons = SmtMetaReduce::isEmbedCons(e);
  (*out) << "  ; " << (isEmbedCons ? "smt-cons: " : "user-decl: ") << cnamek
         << std::endl;
  Expr c = e;
  Expr ct = d_tc.getType(c);
  // (*out) << "  ; type is " << ct << std::endl;
  Attr attr = d_state.getConstructorKind(e.getValue());
  // (*out) << "  ; attr is " << attr << std::endl;
  (*out) << "  (";
  (*out) << cname.str();
  size_t nopqArgs = 0;
  if (attr == Attr::OPAQUE)
  {
    // opaque symbols are non-nullary constructors
    Assert(ct.getKind() == Kind::FUNCTION_TYPE);
    nopqArgs = ct.getNumChildren() - 1;
  }
  else if (attr == Attr::AMB || attr == Attr::AMB_DATATYPE_CONSTRUCTOR)
  {
    nopqArgs = 1;
  }
  for (size_t i = 0; i < nopqArgs; i++)
  {
    (*out) << " (" << cname.str();
    (*out) << ".arg" << (i + 1) << " ";
    // print its type using the utility,
    // which takes into account what the type is in the final embedding
    Expr typ = ct[i];
    if (ct[i].getKind() == Kind::QUOTE_TYPE)
    {
      Expr targ = ct[i][0];
      typ = d_tc.getType(targ);
    }
    std::stringstream sst;
    printEmbType(typ, sst);
    //(*out) << "; Printing datatype argument type " << typ << " gives \"" <<
    // sst.str() << "\" " << termKindToString(tk) << std::endl;
    (*out) << sst.str();
    (*out) << ")";
  }
  (*out) << ")" << std::endl;
}

void ModelSmt::finalize()
{
  // finalize the declarations
  for (const Expr& e : d_declSeen)
  {
    finalizeDecl(e);
  }
  auto replace = [](std::string& txt,
                    const std::string& tag,
                    const std::string& replacement) {
    auto pos = txt.find(tag);
    if (pos != std::string::npos)
    {
      txt.replace(pos, tag.length(), replacement);
    }
  };
  // read the term embedding
  std::stringstream ssiee;
  ssiee << s_plugin_path << "plugins/model_smt/model_eo_embed.eo";
  std::ifstream inepe(ssiee.str());
  std::ostringstream ssepe;
  ssepe << inepe.rdbuf();
  std::string finalEoEmbed = ssepe.str();
  replace(finalEoEmbed, "$SM_TYPE_DECL$", d_embedTypeDt.str());
  replace(finalEoEmbed, "$SM_TERM_DECL$", d_embedTermDt.str());
  replace(finalEoEmbed, "$SM_VALUE_DECL$", d_embedValueDt.str());
  replace(finalEoEmbed, "$SM_EO_TERM_DECL$", d_embedEoTermDt.str());
  // write it back out, will be saved for meta reduce
  std::stringstream ssoee;
  ssoee << s_plugin_path << "plugins/model_smt/model_eo_embed_gen.eo";
  std::ofstream outee(ssoee.str());
  outee << finalEoEmbed;

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
