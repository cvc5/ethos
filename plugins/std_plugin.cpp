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
bool StdPlugin::optionFlattenEval() { return true; }
// this ensures that the types of premises and conclusion must be Bool to
// witness unsoundness
bool StdPlugin::optionVcUseTypeof() { return true; }
// use constraint that conclusion is SMT-LIB input term
bool StdPlugin::optionVcUseIsInput() { return true; }
// use constraint that arguments are SMT-LIB input terms
bool StdPlugin::optionVcUseArgIsInput() { return false; }
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

void StdPlugin::finalizeDeclaration(const Expr& t, std::ostream& os) {}
void StdPlugin::setLiteralTypeRule(Kind k, const Expr& t)
{
  // NOTE: literal definitions cannot use any builtin operators
  // that are desugared in the initial step, e.g. eo::list_*.
  // They can use core eo operators that are desugared later
  // e.g. eo::len.
  std::stringstream ss;
  std::stringstream eoss;
  ss << "(declare-consts ";
  switch (k)
  {
    case Kind::NUMERAL:
      ss << "<numeral>";
      eoss << "Numeral";
      break;
    case Kind::RATIONAL:
      ss << "<rational>";
      eoss << "Rational";
      break;
    case Kind::BINARY:
      ss << "<binary>";
      eoss << "Binary";
      break;
    case Kind::STRING:
      ss << "<string>";
      eoss << "String";
      break;
    case Kind::DECIMAL: ss << "<decimal>"; break;
    case Kind::HEXADECIMAL: ss << "<hexadecimal>"; break;
    default: EO_FATAL() << "Unknown literal type rule" << k << std::endl; break;
  }
  ss << " " << t << ")" << std::endl;
  // declared at the top
  if (!eoss.str().empty())
  {
    // get the symbols and declare them in the preamble
    std::vector<Expr> syms = getSubtermsKind(Kind::CONST, t);
    for (const Expr& s : syms)
    {
      if (d_ltDeclProcessed.find(s) != d_ltDeclProcessed.end())
      {
        continue;
      }
      d_ltDeclProcessed.insert(s);
      finalizeDeclaration(s, d_litTypeDecl);
    }
    d_litTypeDecl << "; type-rules: " << k << std::endl;
    d_litTypeDecl << ss.str();
    // TODO: approximate $eo_Binary as self program
    // it is only possible to define e.g. $eo_Binary
    // if t is ground. This avoids having eo::self as a free parameter.
    // We use $eo_undef_type otherwise.
    if (false && t.isGround())
    {
      d_litTypeDecl << "(define $eo_" << eoss.str() << " () " << t << ")"
                    << std::endl;
    }
    else
    {
      Expr t = d_state.mkSymbol(Kind::CONST, "t", d_state.mkAny());
      Expr ltinst = d_tc.getOrSetLiteralTypeRule(k, t.getValue());
      d_litTypeProg << "(program $eo_lit_type_" << eoss.str()
                    << " ((T Type) (t T))" << std::endl;
      d_litTypeProg << "  :signature (T) Type" << std::endl;
      d_litTypeProg << "  (" << std::endl;
      d_litTypeProg << "  (($eo_lit_type_" << eoss.str() << " t) " << ltinst
                    << ")" << std::endl;
      d_litTypeProg << "  )" << std::endl;
      d_litTypeProg << ")" << std::endl;
      Expr gt = getGroundTermForLiteralKind(k);
      Expr ltg = d_tc.getOrSetLiteralTypeRule(k, gt.getValue());
      if (t.isGround())
      {
        d_litTypeDecl << "; type-rules: " << k << std::endl;
      }
      else
      {
        // FIXME: maybe shouldn't even generate this??
        d_litTypeDecl << "; (approx) type-rules: " << k << std::endl;
      }
      d_litTypeDecl << "(define $eo_" << eoss.str() << " () " << ltg << ")"
                    << std::endl;
      // since $eo_Numeral is used to define the type rules for builtin
      // operators, it must have a ground type.
      if (k == Kind::NUMERAL)
      {
        Assert(t.isGround()) << "Must have a ground type for <numeral>.";
      }
    }
  }
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

}  // namespace ethos
