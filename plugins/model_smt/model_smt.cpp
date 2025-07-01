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
  d_declSeen.insert(e);
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
  std::stringstream preAppEnd;
  for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
  {
    d_eval << std::endl << "    (eo::define ((e" << i << " ($smtx_model_eval x" << i << ")))";
    preAppEnd << ")";
  }
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
  for (Kind kas : argSchemas)
  {
    std::stringstream appConds;
    std::stringstream appCondsEnd;
    if (args.size()>=2)
    {
      appConds << "($smt_apply_2 \"and\" ";
      appCondsEnd << ")";
    }
    std::stringstream appArgs;
    appArgs << " \"" << name << "\"";
    for (size_t i = 1, nargs = args.size(); i <= nargs; i++)
    {
      Kind ka = args[i - 1];
      // use guarded version
      if (i>1)
      {
        appConds << " ";
      }
      if (ka==Kind::PARAM)
      {
        Assert (kas!=Kind::NONE);
        ka = kas;
      }
      if (ka==Kind::BOOLEAN)
      {
        appArgs << " ($smt_apply_1 \"= sm.True\" ";
      }
      else
      {
        // use the selector directly.
        // this is guarded by the ITE
        appArgs << " ($smt_apply_1 \"sm.";
        Assert (d_kindToEoCons.find(ka)!=d_kindToEoCons.end()) << "Could not find " << ka;
        appArgs << d_kindToEoCons[ka] << ".arg1\"";
      }
      appConds << "($sm_is_";
      Assert (d_kindToEoPrefix.find(ka) != d_kindToEoPrefix.end()) << "Could not find kind arg " << ka;
      appConds << d_kindToEoPrefix[ka];
      appConds << " e" << i << ")";
      appArgs << " e" << i << ")";
    }
    d_eval << std::endl << "    ($smt_apply_3 \"ite\" " << appConds.str() << appCondsEnd.str();
    if (args.empty() || args.size() > 3)
    {
      EO_FATAL() << "Unhandled arity " << args.size() << " for " << name;
    }
    d_eval << std::endl << "      ($sm_mk_";
    Kind kr = kret;
    if (kr==Kind::PARAM)
    {
      Assert (kas!=Kind::NONE);
      kr = kas;
    }
    Assert (d_kindToEoPrefix.find(kr) != d_kindToEoPrefix.end()) << "Could not find kind ret " << kr;
    d_eval << d_kindToEoPrefix[kr];
    d_eval << " ($smt_apply_" << args.size() << appArgs.str() << "))";
    preAppEnd << ")";
  }
  d_eval << std::endl << "      " << callApp.str() << ")" << preAppEnd.str() << std::endl;
}

void ModelSmt::printEmbType(const Expr& e, std::ostream& os)
{
  os << e;
}

void ModelSmt::finalizeDeclaration(const Expr& e)
{
  // first, determine which datatype (if any) this belongs to
  std::stringstream ss;
  ss << e;
  std::string sname = ss.str();
  std::stringstream* out = nullptr;
  std::stringstream prefix;
  if (sname.compare(0, 1, "@") == 0 || sname.compare(0, 8, "$eo_List") == 0)
  {
    prefix << "eo.";
    out = &d_embedEoTermDt;
  }
  else
  {
    Expr c = e;
    Expr tc = d_tc.getType(c);
    if (tc.getKind()==Kind::TYPE)
    {
      prefix << "tsm.";
      out = &d_embedTypeDt;
    }
    else
    {
      // otherwise assume an SMT term
      prefix << "sm.";
      out = &d_embedTermDt;
    }
  }
  if (out == nullptr)
  {
    return;
  }
  (*out) << "  ; declare " << e << std::endl;
  Expr c = e;
  Expr ct = d_tc.getType(c);
  // (*out) << "  ; type is " << ct << std::endl;
  Attr attr = d_state.getConstructorKind(e.getValue());
  // (*out) << "  ; attr is " << attr << std::endl;
  (*out) << "  (";
  std::stringstream cname;
  cname << prefix.str() << e;
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
    //sst.str() << "\" " << termKindToString(tk) << std::endl;
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
    finalizeDeclaration(e);
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
  replace(finalEoEmbed, "$SM_EO_TERM_DECL$", d_embedEoTermDt.str());
  replace(finalEoEmbed, "$SM_LITERAL_TYPE_DECL$", d_embedLitType.str());
  // write it back out, will be saved for meta reduce
  std::stringstream ssoee;
  ssoee << s_plugin_path << "plugins/model_smt/model_eo_embed_gen.eo";
  std::ofstream outee(ssoee.str());
  outee << finalEoEmbed;
  
  // read the preamble
  std::stringstream ssiep;
  ssiep << s_plugin_path << "plugins/model_smt/model_eo_preamble.eo";
  std::ifstream inep(ssiep.str());
  std::ostringstream ssep;
  ssep << inep.rdbuf();
  std::string finalEoPremable = ssep.str();

  std::stringstream ssie;
  ssie << s_plugin_path << "plugins/model_smt/model_eo.eo";
  std::ifstream ine(ssie.str());
  std::ostringstream sse;
  sse << ine.rdbuf();
  std::string finalEo = sse.str();
  replace(finalEo, "$EO_TYPE_ENUM_CASES$", d_typeEnum.str());
  replace(finalEo, "$EO_IS_VALUE_CASES$", d_isValue.str());
  replace(finalEo, "$EO_IS_TYPE_CASES$", d_isType.str());
  replace(finalEo, "$EO_CONST_PREDICATE_CASES$", d_constPred.str());
  replace(finalEo, "$EO_EVAL_CASES$", d_customEval.str());

  // now, go back and compile *.eo for the proof rules
  std::stringstream ssis;
  ssis << s_plugin_path << "plugins/model_smt/model_smt.eo";
  std::ifstream ins(ssis.str());
  std::ostringstream sss;
  sss << ins.rdbuf();
  std::string finalSmt = sss.str();
  replace(finalSmt, "$SMT_EVAL_CASES$", d_eval.str());

  std::stringstream ssoe;
  ssoe << s_plugin_path << "plugins/model_smt/model_smt_gen.eo";
  // std::cout << "Write smt-model    " << finalSmt.str() << std::endl;
  std::ofstream oute(ssoe.str());
  // the final user defined signature, as a preamble
  oute << finalEo;
  oute << finalSmt;
}

}  // namespace ethos
