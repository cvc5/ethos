/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "meta_reduce_plugin.h"

#include <fstream>
#include <sstream>

namespace ethos {

MetaReducePlugin::MetaReducePlugin(State& s) : StdPlugin(s)
{
  initializeCommonMetaKinds();
}

MetaReducePlugin::~MetaReducePlugin() {}

void MetaReducePlugin::initializeCommonMetaKinds()
{
  d_typeToMetaKind["$eo_Datatype"] = MetaKind::DATATYPE;
  d_typeToMetaKind["$eo_DatatypeCons"] = MetaKind::DATATYPE_CONSTRUCTOR;
  d_typeToMetaKind["$smt_Model"] = MetaKind::SMT_MODEL;
  d_typeToMetaKind["$smt_RefList"] = MetaKind::SMT_REFLIST;
  d_typeToMetaKind["$smt_Term"] = MetaKind::SMT;
  d_typeToMetaKind["$smt_Type"] = MetaKind::SMT_TYPE;
  d_typeToMetaKind["$smt_Value"] = MetaKind::SMT_VALUE;
  d_typeToMetaKind["$smt_Map"] = MetaKind::SMT_MAP;
  d_typeToMetaKind["$smt_Seq"] = MetaKind::SMT_SEQ;
  d_typeToMetaKind["$smt_Datatype"] = MetaKind::SMT_DATATYPE;
  d_typeToMetaKind["$smt_DatatypeCons"] = MetaKind::SMT_DATATYPE_CONSTRUCTOR;
  d_typeToMetaKind["$smt_BuiltinType"] = MetaKind::SMT_BUILTIN;

  d_prefixToMetaKind["edt"] = MetaKind::DATATYPE;
  d_prefixToMetaKind["edtc"] = MetaKind::DATATYPE_CONSTRUCTOR;
  d_prefixToMetaKind["sm"] = MetaKind::SMT;
  d_prefixToMetaKind["tsm"] = MetaKind::SMT_TYPE;
  d_prefixToMetaKind["vsm"] = MetaKind::SMT_VALUE;
  d_prefixToMetaKind["msm"] = MetaKind::SMT_MAP;
  d_prefixToMetaKind["ssm"] = MetaKind::SMT_SEQ;
  d_prefixToMetaKind["dt"] = MetaKind::SMT_DATATYPE;
  d_prefixToMetaKind["dtc"] = MetaKind::SMT_DATATYPE_CONSTRUCTOR;
}

void MetaReducePlugin::bind(const std::string&, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  finalizeDecl(e);
}

std::string MetaReducePlugin::getName(const Expr& e)
{
  std::stringstream ss;
  if (e.getNumChildren() == 0)
  {
    ss << e;
  }
  return ss.str();
}

bool MetaReducePlugin::isEmbedCons(const Expr& e)
{
  std::string sname = getName(e);
  return (sname.compare(0, 5, "$emb_") == 0);
}

bool MetaReducePlugin::isSmtApplyApp(const Expr& oApp)
{
  if (oApp.getKind() != Kind::APPLY_OPAQUE || oApp.getNumChildren() <= 1
      || oApp[1].getKind() != Kind::STRING)
  {
    return false;
  }
  std::string sname = getName(oApp[0]);
  return (sname.compare(0, 11, "$smt_apply_") == 0
          || sname.compare(0, 10, "$smt_type_") == 0
          || sname.compare(0, 13, "$smt_datatype") == 0);
}

MetaKind MetaReducePlugin::prefixToMetaKind(const std::string& str,
                                            MetaKind elseKind) const
{
  std::map<std::string, MetaKind>::const_iterator it =
      d_prefixToMetaKind.find(str);
  if (it != d_prefixToMetaKind.end())
  {
    return it->second;
  }
  return elseKind;
}

MetaKind MetaReducePlugin::getTypeMetaKindFor(const Expr& typ,
                                              MetaKind elseKind,
                                              bool followFunctionRange) const
{
  Kind k = typ.getKind();
  if (k == Kind::APPLY_OPAQUE)
  {
    std::string sname = getName(typ[0]);
    if (sname.compare(0, 10, "$smt_type_") == 0)
    {
      return MetaKind::SMT_BUILTIN;
    }
    if (sname.compare(0, 13, "$smt_datatype") == 0)
    {
      return MetaKind::SMT_BUILTIN_DATATYPE;
    }
  }
  if (followFunctionRange && k == Kind::FUNCTION_TYPE)
  {
    return getTypeMetaKindFor(typ[typ.getNumChildren() - 1],
                              elseKind,
                              followFunctionRange);
  }
  std::string sname = getName(typ);
  std::map<std::string, MetaKind>::const_iterator it =
      d_typeToMetaKind.find(sname);
  if (it != d_typeToMetaKind.end())
  {
    return it->second;
  }
  return elseKind;
}

MetaKind MetaReducePlugin::getMetaKindFor(const Expr& e,
                                          std::string& cname) const
{
  std::string sname = getName(e);
  if (isBuiltinMetaSymbol(sname))
  {
    cname = sname;
    return MetaKind::SMT_BUILTIN;
  }
  if (sname.compare(0, 2, "@@") == 0 || sname.compare(0, 4, "$eo_") == 0)
  {
    cname = sname;
    return MetaKind::EUNOIA;
  }
  if (isEmbedCons(e))
  {
    cname = sname.substr(5);
    size_t firstDot = cname.find('.');
    if (firstDot == std::string::npos)
    {
      return MetaKind::EUNOIA;
    }
    std::string prefix = cname.substr(0, firstDot);
    cname = cname.substr(firstDot + 1);
    return prefixToMetaKind(prefix);
  }
  cname = sname;
  return MetaKind::EUNOIA;
}

bool MetaReducePlugin::buildLambdaDefineProgram(const std::string& name,
                                                const Expr& e,
                                                Expr& symbol,
                                                Expr& prog)
{
  if (name.compare(0, 4, "$eo_") != 0 || e.getKind() != Kind::LAMBDA)
  {
    return false;
  }

  std::vector<Expr> argTypes;
  Assert(e[0].getKind() == Kind::TUPLE);
  Assert(e[0].getNumChildren() != 0);
  for (size_t i = 0, nargs = e[0].getNumChildren(); i < nargs; i++)
  {
    Expr arg = e[0][i];
    argTypes.push_back(d_tc.getType(arg));
  }
  Expr retType = allocateTypeVariable();
  Expr pt = d_state.mkProgramType(argTypes, retType);
  symbol = d_state.mkSymbol(Kind::PROGRAM_CONST, name, pt);

  std::vector<Expr> appChildren;
  appChildren.push_back(symbol);
  for (size_t i = 0, nargs = e[0].getNumChildren(); i < nargs; i++)
  {
    appChildren.push_back(e[0][i]);
  }
  Expr progApp = d_state.mkExprSimple(Kind::APPLY, appChildren);
  Expr pcase = d_state.mkPair(progApp, e[1]);
  prog = d_state.mkExprSimple(Kind::PROGRAM, {pcase});
  return true;
}

bool MetaReducePlugin::beginFinalizeDecl(const Expr& e)
{
  if (d_declSeen.find(e) != d_declSeen.end())
  {
    return false;
  }
  d_declSeen.insert(e);
  return true;
}

bool MetaReducePlugin::isProgramApp(const Expr& app)
{
  return (app.getKind() == Kind::APPLY
          && app[0].getKind() == Kind::PROGRAM_CONST);
}

std::string MetaReducePlugin::emitResourceFile(
    const std::string& resourcePath,
    const std::string& outputPath,
    const std::vector<Replacement>& replacements,
    bool replAll) const
{
  std::ifstream in(getResourcePath(resourcePath));
  if (!in.is_open())
  {
    EO_FATAL() << "MetaReducePlugin: failed to open resource " << resourcePath;
  }

  std::ostringstream ss;
  ss << in.rdbuf();
  std::string rendered = ss.str();
  for (const Replacement& repl : replacements)
  {
    if (replAll)
    {
      rendered = replace_all(rendered, repl.first, repl.second);
    }
    else
    {
      replace(rendered, repl.first, repl.second);
    }
  }

  std::string outPath = getOutputPath(outputPath);
  std::ofstream out(outPath);
  if (!out.is_open())
  {
    EO_FATAL() << "MetaReducePlugin: failed to open output " << outPath;
  }
  out << rendered;
  return outPath;
}

}  // namespace ethos
