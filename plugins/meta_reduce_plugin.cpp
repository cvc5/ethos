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

#include "base/output.h"
#include "literal.h"
#include "utils.h"

namespace ethos {

namespace {

/**
 * Strip the eo::requires guards from t. The range of a function type may be
 * wrapped in such guards, see State::mkRequires.
 */
Expr stripRequires(const Expr& t)
{
  Expr ret = t;
  while (ret.getKind() == Kind::EVAL_REQUIRES)
  {
    ret = ret[2];
  }
  return ret;
}

}  // namespace

MetaReducePlugin::MetaReducePlugin(State& s, ConjectureType conjType)
    : StdPlugin(s), d_conjectureType(conjType)
{
  initializeCommonMetaKinds();
}

MetaReducePlugin::~MetaReducePlugin() {}

ConjectureType MetaReducePlugin::optionMetaConjectureType() const
{
  return d_conjectureType;
}

void MetaReducePlugin::initializeCommonMetaKinds()
{
  // Note that the types of the deep embedding whose constructors are static
  // in the backend templates are not listed here; they are declared via the
  // $native_embed_* symbols in the Eunoia templates, which carry their
  // embedded names (see getTypeMetaKindFor and getEmbedTypeName).
  d_typeToMetaKind["$smt_Term"] = MetaKind::SMT;
  d_typeToMetaKind["$smt_Type"] = MetaKind::SMT_TYPE;
  d_typeToMetaKind["$smt_Value"] = MetaKind::SMT_VALUE;
  d_typeToMetaKind["$smt_Map"] = MetaKind::SMT_MAP;
  d_typeToMetaKind["$smt_Seq"] = MetaKind::SMT_SEQ;
  d_typeToMetaKind["$native_BuiltinType"] = MetaKind::SMT_BUILTIN;

  d_prefixToMetaKind["sm"] = MetaKind::SMT;
  d_prefixToMetaKind["tsm"] = MetaKind::SMT_TYPE;
  d_prefixToMetaKind["vsm"] = MetaKind::SMT_VALUE;
  d_prefixToMetaKind["msm"] = MetaKind::SMT_MAP;
  d_prefixToMetaKind["ssm"] = MetaKind::SMT_SEQ;
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
  if (e.getNumChildren() != 0)
  {
    return "";
  }
  // Note we take the name of the literal here and not the printed form of e,
  // which would add SMT-LIB quoting for symbols that are not simple symbols.
  // For example, a symbol declared as |foo bar| is bound to the name "foo bar"
  // and must be handed to the backends as such.
  const Literal* l = e.getValue()->asLiteral();
  if (l != nullptr)
  {
    return l->toString();
  }
  // Atomic terms that are not literals, e.g. Type, are printed by their
  // builtin name.
  std::stringstream ss;
  ss << e;
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
  return (sname.compare(0, 14, "$native_apply_") == 0
          || sname.compare(0, 13, "$native_type_") == 0);
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
  // the type may be guarded, in which case we classify the type it guards
  Expr t = stripRequires(typ);
  Kind k = t.getKind();
  if (k == Kind::APPLY_OPAQUE)
  {
    std::string sname = getName(t[0]);
    if (sname.compare(0, 13, "$native_type_") == 0)
    {
      return MetaKind::SMT_BUILTIN;
    }
    if (sname == "$native_embed_eo")
    {
      return MetaKind::EO_EMBED;
    }
    if (sname == "$native_embed_smt")
    {
      return MetaKind::SMT_EMBED;
    }
    if (sname == "$native_embed_checker")
    {
      return MetaKind::CHECKER_EMBED;
    }
  }
  if (followFunctionRange && k == Kind::FUNCTION_TYPE)
  {
    return getTypeMetaKindFor(
        t[t.getNumChildren() - 1], elseKind, followFunctionRange);
  }
  std::string sname = getName(t);
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
    MetaKind mk = prefixToMetaKind(prefix, MetaKind::NONE);
    if (mk != MetaKind::NONE)
    {
      return mk;
    }
    // Otherwise the constructor may belong to a datatype declared via a
    // $native_embed_* type, in which case we classify it by its return type.
    Expr app = getEmbedTypeApp(e.getType());
    if (!app.isNull())
    {
      return getTypeMetaKindFor(app, MetaKind::EUNOIA, false);
    }
    return MetaKind::EUNOIA;
  }
  cname = sname;
  return MetaKind::EUNOIA;
}

Expr MetaReducePlugin::getEmbedTypeApp(const Expr& typ)
{
  // note the range of a function type may be guarded
  Expr t = stripRequires(typ);
  while (t.getKind() == Kind::FUNCTION_TYPE)
  {
    t = stripRequires(t[t.getNumChildren() - 1]);
  }
  // we require the shape expected by getEmbedTypeName below, i.e. an
  // application to a single SMT-LIB identifier
  if (t.getKind() == Kind::APPLY_OPAQUE && t.getNumChildren() == 2
      && t[1].getKind() == Kind::STRING)
  {
    std::string sname = getName(t[0]);
    if (sname.compare(0, 14, "$native_embed_") == 0)
    {
      return t;
    }
  }
  return Expr();
}

std::string MetaReducePlugin::getEmbedTypeName(const Expr& app)
{
  if (app.getKind() != Kind::APPLY_OPAQUE || app.getNumChildren() != 2
      || app[1].getKind() != Kind::STRING)
  {
    EO_FATAL() << "MetaReducePlugin: bad embed type application " << app;
  }
  return getName(app[1]);
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
  Expr progApp = d_state.mkExpr(Kind::APPLY, appChildren);
  Expr pcase = d_state.mkPair(progApp, e[1]);
  prog = d_state.mkExpr(Kind::PROGRAM, {pcase});
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

}  // namespace ethos
