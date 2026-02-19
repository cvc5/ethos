/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "std_plugin.h"

#include <fstream>
#include <sstream>
#include <string>

#include "state.h"

namespace ethos {

#if 0
std::string StdPlugin::s_plugin_path = "/home/andrew/ethos/";
#else
std::string StdPlugin::s_plugin_path =
    "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
#endif

// enables eager elimination of nested evaluation, ite, and requires
bool StdPlugin::optionFlattenEval() { return false; }
// this ensures that the types of premises and conclusion must be Bool to
// witness unsoundness
bool StdPlugin::optionVcUseTypeof() { return true; }
// strict means we are not debugging completeness
bool StdPlugin::optionVcUseModelStrict() { return true; }
// uses trigger in final encoding
bool StdPlugin::optionSmtMetaUseTriggers() { return true; }
// makes conjecture easy to debug models
bool StdPlugin::optionSmtMetaDebugConjecture() { return false; }
// type of conjecture
ConjectureType StdPlugin::optionSmtMetaConjectureType() const
{
  if (d_state.getOptions().d_pluginSmtMetaSygus)
  {
    return ConjectureType::SYGUS;
  }
  return ConjectureType::VC;
}
// whether we are optimizing with a sygus grammar
bool StdPlugin::optionSmtMetaSygusGrammar() { return true; }
// whether the sygus grammar is designed to enumerate well-typed terms
bool StdPlugin::optionSmtMetaSygusGrammarWellTyped() { return true; }

StdPlugin::StdPlugin(State& s) : d_state(s), d_tc(s.getTypeChecker())
{
  d_typeVarCounter = 0;
}

StdPlugin::~StdPlugin() {}

Expr StdPlugin::lookupVar(const std::string& name)
{
  Expr e = d_state.getVar(name);
  if (e.isNull())
  {
    EO_FATAL() << "StdPlugin::lookupVar: Symbol " << name << " must be defined";
  }
  return e;
}

std::vector<Expr> StdPlugin::getSubtermsKind(Kind k, const Expr& t)
{
  std::vector<Expr> ret;
  std::set<Expr> visited;
  std::vector<Expr> toVisit;
  toVisit.push_back(t);
  Expr cur;
  do
  {
    cur = toVisit.back();
    toVisit.pop_back();
    if (visited.find(cur) != visited.end())
    {
      continue;
    }
    visited.insert(cur);
    if (cur.getKind() == k)
    {
      ret.push_back(cur);
    }
    for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
    {
      toVisit.push_back(cur[i]);
    }
  } while (!toVisit.empty());
  return ret;
}

bool StdPlugin::hasSubterm(const Expr& t, const Expr& s)
{
  std::unordered_set<const ExprValue*> visited;
  std::vector<Expr> toVisit;
  toVisit.push_back(t);
  Expr cur;
  while (!toVisit.empty())
  {
    cur = toVisit.back();
    toVisit.pop_back();
    const ExprValue* cv = cur.getValue();
    if (visited.find(cv) != visited.end())
    {
      continue;
    }
    visited.insert(cv);
    if (cur == s)
    {
      return true;
    }
    for (size_t i = 0, nchildren = cur.getNumChildren(); i < nchildren; i++)
    {
      toVisit.push_back(cur[i]);
    }
  }
  return false;
}

Expr StdPlugin::allocateTypeVariable()
{
  d_typeVarCounter++;
  std::stringstream ss;
  ss << "$eoT_" << d_typeVarCounter;
  return d_state.mkSymbol(Kind::PARAM, ss.str(), d_state.mkType());
}

Expr StdPlugin::getGroundTermForLiteralKind(Kind k)
{
  Expr gt;
  switch (k)
  {
    case Kind::NUMERAL: gt = d_state.mkLiteral(k, "0"); break;
    case Kind::RATIONAL: gt = d_state.mkLiteral(k, "0/1"); break;
    case Kind::BINARY: gt = d_state.mkLiteral(k, "0"); break;
    case Kind::STRING: gt = d_state.mkLiteral(k, ""); break;
    default: break;
  }
  return gt;
}

std::string StdPlugin::literalKindToString(Kind k)
{
  std::stringstream ss;
  switch (k)
  {
    case Kind::NUMERAL: ss << "<numeral>"; break;
    case Kind::RATIONAL: ss << "<rational>"; break;
    case Kind::BINARY: ss << "<binary>"; break;
    case Kind::STRING: ss << "<string>"; break;
    case Kind::DECIMAL: ss << "<decimal>"; break;
    case Kind::HEXADECIMAL: ss << "<hexadecimal>"; break;
    default: EO_FATAL() << "Unknown literal type rule" << k << std::endl; break;
  }
  return ss.str();
}

void StdPlugin::replace(std::string& txt,
                const std::string& tag,
                const std::string& replacement) {
  auto pos = txt.find(tag);
  if (pos != std::string::npos)
  {
    txt.replace(pos, tag.length(), replacement);
  }
}
  
std::string StdPlugin::replace_all(std::string str,
                        const std::string& from,
                        const std::string& to)
{
  if (from.empty()) return str;  // avoid infinite loop

  std::size_t pos = 0;
  while ((pos = str.find(from, pos)) != std::string::npos)
  {
    str.replace(pos, from.length(), to);
    pos += to.length();  // move past the replacement
  }
  return str;
}
}  // namespace ethos
