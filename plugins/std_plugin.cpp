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

//std::string  StdPlugin::s_plugin_path = "/home/andrew/ethos/";
std::string StdPlugin::s_plugin_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";

StdPlugin::StdPlugin(State& s) : d_state(s), d_tc(s.getTypeChecker()) {}

StdPlugin::~StdPlugin() {}

void StdPlugin::finalizeDeclaration(const Expr& t, std::ostream& os) {}
void StdPlugin::setLiteralTypeRule(Kind k, const Expr& t)
{
  // NOTE: literal definitions cannot use any builtin operators
  // that are desugared in the initial step, e.g. eo::list_*.
  // They can use core eo operators that are desugared later
  // e.g. eo::len.
  std::stringstream ss;
  ss << "(declare-consts ";
  std::ostream* os;
  switch (k)
  {
    case Kind::NUMERAL:
      ss << "<numeral>";
      os = &d_ltNum;
      break;
    case Kind::RATIONAL:
      ss << "<rational>";
      os = &d_ltRational;
      break;
    case Kind::BINARY:
      ss << "<binary>";
      os = &d_ltBinary;
      break;
    case Kind::STRING:
      ss << "<string>";
      os = &d_ltString;
      break;
    case Kind::DECIMAL: ss << "<decimal>"; break;
    case Kind::HEXADECIMAL: ss << "<hexadecimal>"; break;
    default: EO_FATAL() << "Unknown literal type rule" << k << std::endl; break;
  }
  ss << " " << t << ")" << std::endl;
  // declared at the top
  if (os != nullptr)
  {
    // it is only possible to define e.g. $eo_Binary
    // if t is ground. This avoids having eo::self as a free parameter.
    // We use $eo_undef_type otherwise.
    if (t.isGround())
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
      (*os) << t;
    }
    else
    {
      // since $eo_Numeral is used to define the type rules for builtin
      // operators, it must have a ground type.
      if (k == Kind::NUMERAL)
      {
        EO_FATAL() << "Must have a ground type for <numeral>.";
      }
      (*os) << "$eo_undef_type";
    }
  }
  else
  {
    d_litTypeDecl << "; type-rules: " << k << std::endl;
    d_litTypeDecl << ss.str();
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

}  // namespace ethos
