/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "trim_defs.h"

#include <fstream>
#include <sstream>
#include <string>

#include "state.h"

namespace ethos {

TrimList::TrimList(State& s) : d_state(s)
{
}

std::vector<std::pair<Expr, Expr>> TrimList::getTrimList(const Expr& e)
{
  std::map<Expr, bool> visited;
  return getTrimList(e, visited);
}

std::vector<std::pair<Expr, Expr>> TrimList::getTrimList(const Expr& e, std::map<Expr, bool>& visited)
{
  std::vector<std::pair<Expr, Expr>> tlist;
  std::set<Expr> fwdDecl;
  TypeChecker& tcheck = d_state.getTypeChecker();
  std::map<Expr, bool>::iterator it;
  std::vector<Expr> toVisit;
  toVisit.push_back(e);
  Expr cur;
  do
  {
    cur = toVisit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      Kind k = cur.getKind();
      if (k == Kind::CONST || k == Kind::PROGRAM_CONST || k == Kind::PROOF_RULE)
      {
        visited[cur] = false;
        // we track the definitions in its type
        Expr tc = tcheck.getType(cur);
        toVisit.push_back(tc);
        if (k == Kind::PROGRAM_CONST)
        {
          Expr pc = d_state.getProgram(cur.getValue());
          if (!pc.isNull())
          {
            it = visited.find(pc);
            if (it != visited.end() && !it->second)
            {
              // if we are already visiting this program, it must be a forward declaration
              toVisit.pop_back();
              // avoid forward declaring more than once with the fwdDecl set
              if (fwdDecl.find(cur)==fwdDecl.end())
              {
                fwdDecl.insert(cur);
                tlist.emplace_back(cur, d_null);
              }
            }
            else
            {
              // otherwise, we track the definitions in its body
              toVisit.push_back(pc);
            }
          }
        }
      }
      else
      {
        // an ordinary application
        // we are done with this node
        visited[cur] = true;
        toVisit.pop_back();
        // visit the children
        for (size_t i = 0, nc = cur.getNumChildren(); i < nc; i++)
        {
          toVisit.push_back(cur[i]);
        }
      }
      continue;
    }
    toVisit.pop_back();
    if (!it->second)
    {
      visited[cur] = true;
      // store that this is the official definition
      Expr cval;
      if (cur.getKind() == Kind::PROGRAM_CONST)
      {
        cval = d_state.getProgram(cur.getValue());
      }
      tlist.emplace_back(cur, cval);
    }
  }
  while (toVisit.empty());
  return tlist;
}

//std::string s_td_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
std::string s_td_path = "/home/andrew/ethos/";

TrimDefs::TrimDefs(State& s) : d_state(s), d_tc(s.getTypeChecker())
{
  d_timeStamp = 0;
  d_setDefTarget = false;
}

TrimDefs::~TrimDefs() {}

void TrimDefs::setLiteralTypeRule(Kind k, const Expr& t)
{
  d_litTypeTimestamp[d_timeStamp] = k;
  d_litTypeRule[k] = t;
  ++d_timeStamp;
}

void TrimDefs::bind(const std::string& name, const Expr& e)
{
  Kind k = e.getKind();
  if (k == Kind::CONST || k == Kind::PROOF_RULE)
  {
    d_declTimestamp[e] = d_timeStamp;
    ++d_timeStamp;
  }
}

void TrimDefs::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  d_attrDecl[v] = std::pair<Attr, Expr>(a, cons);
}

void TrimDefs::defineProgram(const Expr& v, const Expr& prog)
{
  if (d_declTimestamp.find(v)!=d_declTimestamp.end())
  {
    d_declTimestamp[v] = d_timeStamp;
    ++d_timeStamp;
  }
}

void TrimDefs::markOracleCmd(const Expr& v, const std::string& ocmd)
{
  std::stringstream ss;
  ss << v;
  std::string vname = ss.str();
  if (vname=="$trim_defs_target")
  {
    d_defTarget = ocmd;
    d_setDefTarget = true;
  }
}

void TrimDefs::printTerm(const Expr& t, std::ostream& os)
{
  // no santization necessary
  os << t;
}

void TrimDefs::printSetLiteralTypeRule(Kind k, const Expr& t)
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
  d_defs << "; type-rules " << ss.str() << std::endl;
  d_defs << "(declare-consts ";
  d_defs << ss.str() << " " << t << ")" << std::endl;
}

void TrimDefs::printProgram(const Expr& e, const Expr& prog)
{
  Expr p = e;
  Expr pt = d_tc.getType(p);
  std::vector<Expr> pandt{pt, prog};
  std::vector<Expr> vars = Expr::getVariables(pandt);
  d_defs << "; " << (prog.isNull() ? "fwd-decl: " : "program: ") << e
         << std::endl;
  d_defs << "(program " << e << " (";
  std::vector<Expr> params;
  printParamList(vars, d_defs, params, false);
  d_defs << ")" << std::endl;
  Assert(pt.getKind() == Kind::PROGRAM_TYPE);
  Assert(pt.getNumChildren() > 1);
  d_defs << "  :signature (";
  size_t pargs = pt.getNumChildren() - 1;
  for (size_t i = 0; i < pargs; i++)
  {
    if (i > 0)
    {
      d_defs << " ";
    }
    printTerm(pt[i], d_defs);
  }
  d_defs << ") ";
  printTerm(pt[pargs], d_defs);
  d_defs << std::endl;
  if (!prog.isNull())
  {
    d_defs << "  (" << std::endl;
    for (size_t i = 0, ncases = prog.getNumChildren(); i < ncases; i++)
    {
      const Expr& c = prog[i];
      d_defs << "  (";
      printTerm(c[0], d_defs);
      d_defs << " ";
      printTerm(c[1], d_defs);
      d_defs << ")" << std::endl;
    }
    d_defs << "  )" << std::endl;
  }
  d_defs << ")" << std::endl;
}

void TrimDefs::printDeclaration(const Expr& e)
{
  Expr c = e;
  Attr cattr = Attr::NONE;
  Expr cattrCons;
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  it = d_attrDecl.find(e);
  if (it != d_attrDecl.end())
  {
    cattr = it->second.first;
    cattrCons = it->second.second;
  }
  /*
  if (cattr == Attr::DATATYPE)
  {
    printDatatype(e);
    return;
  }
  */
  if (cattr == Attr::DATATYPE_CONSTRUCTOR
      || cattr == Attr::AMB_DATATYPE_CONSTRUCTOR)
  {
    // should be handled as part of datatype
    return;
  }
  // check for eo::List
  std::stringstream cnss;
  cnss << c;
  std::string cname = cnss.str();
  if (cname.compare(0, 4, "eo::") == 0)
  {
    return;
  }
  Expr cto = d_tc.getType(c);
  Expr ct = cto;
  std::vector<Expr> argTypes;
  Expr retType;
  std::map<Expr, bool> visited;
  bool firstParam = true;
  std::vector<Expr> params;
  std::stringstream opaqueArgs;
  if (ct.getKind() == Kind::FUNCTION_TYPE)
  {
    if (cattr == Attr::OPAQUE)
    {
      size_t novars = ct.getNumChildren() - 1;
      for (size_t i = 0; i < novars; i++)
      {
        Assert(ct[i].getKind() == Kind::QUOTE_TYPE)
            << "Bad opaque function type " << ct << " for " << c;
        Expr v = ct[i][0];
        if (v.getKind() == Kind::ANNOT_PARAM)
        {
          v = v[0];
        }
        Assert(v.getKind() == Kind::PARAM)
            << "Bad opaque function variable " << ct << " for " << c;
        std::vector<Expr> vars;
        vars.push_back(v);
        printParamList(
            vars, opaqueArgs, params, true, visited, firstParam, true);
      }
      ct = ct[novars];
    }
    std::pair<std::vector<Expr>, Expr> ftype = ct.getFunctionType();
    argTypes = ftype.first;
    retType = ftype.second;
  }
  else
  {
    retType = ct;
  }
  d_defs << "; declare: " << e << std::endl;
  d_defs << "(declare-";
  std::vector<Expr> vars = Expr::getVariables(ct);
  if (!vars.empty())
  {
    d_defs << "parameterized-const " << cname << " (" << opaqueArgs.str();
    size_t pcount = 0;
    for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
    {
      Expr at = argTypes[i];
      Kind ak = at.getKind();
      if (ak == Kind::QUOTE_TYPE)
      {
        Expr v = at[0];
        if (v.getKind() == Kind::ANNOT_PARAM)
        {
          v = v[0];
        }
        if (v.getKind() == Kind::PARAM)
        {
          std::vector<Expr> vars;
          vars.push_back(v);
          printParamList(vars, d_defs, params, true, visited, firstParam);
        }
        else if ((cattr == Attr::AMB || cattr == Attr::AMB_DATATYPE_CONSTRUCTOR) && i == 0)
        {
          // print the parameters; these will lead to a definition that is
          // ambiguous again.
          std::vector<Expr> avars = Expr::getVariables(v);
          printParamList(vars, d_defs, params, true, visited, firstParam);
        }
        else
        {
          Assert(false) << "Non-param quote " << ct << " for " << c;
        }
      }
      else
      {
        // otherwise ordinary type
        pcount++;
        std::stringstream ssp;
        ssp << "$eo_x_" << pcount;
        Expr v = d_state.mkSymbol(Kind::PARAM, ssp.str(), at);
        std::vector<Expr> vars;
        vars.push_back(v);
        printParamList(vars, d_defs, params, true, visited, firstParam);
      }
    }
    d_defs << ") ";
    printTerm(retType, d_defs);
    d_defs << ")" << std::endl;
  }
  else
  {
    d_defs << "const " << cname << " ";
    printTerm(ct, d_defs);
  }
  if (cattr != Attr::NONE)
  {
    d_defs << std::endl;
    d_defs << "  :" << cattr;
    if (cattrCons.isNull())
    {
      d_defs << " " << cattrCons;
    }
  }
  d_defs << ")" << std::endl;
}

void TrimDefs::printParamList(const std::vector<Expr>& vars,
                             std::ostream& os,
                             std::vector<Expr>& params,
                             bool useImplicit)
{
  std::map<Expr, bool> visited;
  bool firstParam = true;
  printParamList(vars, os, params, useImplicit, visited, firstParam);
}

void TrimDefs::printParamList(const std::vector<Expr>& vars,
                             std::ostream& os,
                             std::vector<Expr>& params,
                             bool useImplicit,
                             std::map<Expr, bool>& visited,
                             bool& firstParam,
                             bool isOpaque)
{
  std::map<Expr, bool>::iterator itv;
  std::vector<Expr> toVisit(vars.begin(), vars.end());
  Expr cur;
  while (!toVisit.empty())
  {
    cur = toVisit.back();
    Assert(cur.getKind() == Kind::PARAM);
    itv = visited.find(cur);
    if (itv != visited.end() && itv->second)
    {
      toVisit.pop_back();
      continue;
    }
    Expr tcur = d_tc.getType(cur);
    if (itv == visited.end())
    {
      visited[cur] = false;
      // ensure its type has been printed
      Assert(!tcur.isNull());
      std::vector<Expr> tvars = Expr::getVariables(tcur);
      toVisit.insert(toVisit.end(), tvars.begin(), tvars.end());
      continue;
    }
    else if (!itv->second)
    {
      Assert(!itv->second);
      visited[cur] = true;
      if (firstParam)
      {
        firstParam = false;
      }
      else
      {
        os << " ";
      }
      os << "(" << cur << " ";
      printTerm(tcur, os);
      if (std::find(vars.begin(), vars.end(), cur) == vars.end())
      {
        if (useImplicit)
        {
          os << " :implicit";
        }
      }
      else if (isOpaque)
      {
        os << " :opaque";
      }
      os << ")";
      toVisit.pop_back();
      params.push_back(cur);
    }
  }
}

void TrimDefs::printDefinition(const std::string& name, const Expr& t)
{
  Assert(t.getKind() == Kind::LAMBDA);
  d_defs << "; define: " << name << std::endl;
  d_defs << "(define " << name << " (";
  std::vector<Expr> vars;
  for (size_t i = 0, nvars = t[0].getNumChildren(); i < nvars; i++)
  {
    vars.push_back(t[0][i]);
  }
  std::vector<Expr> params;
  printParamList(vars, d_defs, params, true);
  d_defs << ")" << std::endl;
  d_defs << "  ";
  printTerm(t[1], d_defs);
  d_defs << ")" << std::endl;
}

void TrimDefs::printRule(const Expr& e)
{
  //std::cout << "Finalize rule " << e << std::endl;
  Expr r = e;
  Expr rto = d_tc.getType(r);

  d_defs << "; rule: " << e << std::endl;
  d_defs << "(declare-rule " << e << "(";
  d_defs << ")" << std::endl;

  Attr rattr = Attr::NONE;
  Expr rattrCons;
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  it = d_attrDecl.find(e);
  if (it != d_attrDecl.end())
  {
    rattr = it->second.first;
    rattrCons = it->second.second;
  }
  if (rattr!=Attr::NONE)
  {
    // handle :assumption, :conclusion-explicit here.
  }

  Expr rt = d_tc.getType(r);
  Expr conct = rt;
  std::stringstream paramList;
  std::stringstream ssArgs;
  std::stringstream ssPremises;
  bool firstPremise = true;
  bool firstArg = true;
  if (rt.getKind()==Kind::FUNCTION_TYPE)
  {
    for (size_t i = 1, nargs = rt.getNumChildren(); i < nargs; i++)
    {
      Expr argType = rt[i - 1];
      Kind k = argType.getKind();
      if (k==Kind::PROOF_TYPE)
      {
        if (firstPremise)
        {
          firstPremise = false;
        }
        else
        {
          ssPremises << " ";
        }
        ssPremises << argType[0];
      }
      else if (k==Kind::QUOTE_TYPE)
      {
        if (firstArg)
        {
          firstArg = false;
        }
        else
        {
          ssArgs << " ";
        }
        ssArgs << argType[0];
      }
    }
    conct = rt[rt.getNumChildren()-1];
  }
  if (!firstArg)
  {
    d_defs << "  :args (" << ssArgs.str() << ")" << std::endl;
  }
  if (!firstPremise)
  {
    d_defs << "  :premises (" << ssPremises.str() << ")" << std::endl;
  }
  if (rt.getKind()==Kind::EVAL_REQUIRES)
  {
    d_defs << "  :requires (";
    bool firstRequires = true;
    while (rt.getKind()==Kind::EVAL_REQUIRES)
    {
      if (firstRequires)
      {
        firstRequires = false;
      }
      else
      {
        d_defs << " ";
      }
      d_defs << "(" << rt[0] << " " << rt[1] << ")";
      rt = rt[2];
    }
    while (rt.getKind()==Kind::EVAL_REQUIRES);
  }
  d_defs << "  :conclusion " << rt << std::endl;
  if (d_state.isProofRuleSorry(e.getValue()))
  {
    d_defs << "  :sorry" << std::endl;
  }
  d_defs << ")" << std::endl;
}

void TrimDefs::printDatatype(const Expr& e)
{
  /*
  Expr d = e;
  Expr dt = d_tc.getType(d);
  Attr dattr = Attr::NONE;
  Expr dattrCons;
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  it = d_attrDecl.find(e);
  if (it != d_attrDecl.end())
  {
    dattr = it->second.first;
    dattrCons = it->second.second;
  }
  Assert(dattr == Attr::DATATYPE);
  d_defs << "; datatype: " << e << " " << dattrCons << std::endl;
  d_defs << "(declare-datatypes (";
  d_defs << ")" << std::endl;
  // TODO
  d_defs << ")" << std::endl;
  */
}

void TrimDefs::finalize()
{
  if (!d_setDefTarget)
  {
    EO_FATAL() << "Must set target with (declare-oracle-fun $trim_def_target <type> <definition to trim>)" << std::endl;
  }
  // proof rules and other definitions are stored separately.
  Expr v = d_state.getProofRule(d_defTarget);
  if (v.isNull())
  {
    v = d_state.getVar(d_defTarget);
  }
  if (v.isNull())
  {
    EO_FATAL() << "Could not find target definition \"" << d_defTarget << "\"" << std::endl;
  }
  TrimList tlist(d_state);
  std::vector<std::pair<Expr, Expr>> tl = tlist.getTrimList(v);

  // the timestamps where literal types were declared
  std::vector<size_t> tsLits;
  for (std::pair<size_t, Kind> lt : d_litTypeTimestamp)
  {
    tsLits.push_back(lt.first);
  }
  // standard sort
  std::sort(tsLits.begin(), tsLits.end());
  size_t tsLitsIndex = 0;

  for (size_t i=0, ntl=tl.size(); i<ntl; i++)
  {
    Expr c = tl[i].first;
    Expr cval = tl[i].second;
    Assert (d_declTimestamp.find(c)!=d_declTimestamp.end());
    size_t tsc = d_declTimestamp[c];
    // see if we need to print a literal type rule at this point
    while (tsLitsIndex<tsLits.size() && tsLits[tsLitsIndex]<tsc)
    {
      size_t il = tsLits[tsLitsIndex];
      Assert (d_litTypeTimestamp.find(il)!=d_litTypeTimestamp.end());
      Kind k = d_litTypeTimestamp[il];
      Assert (d_litTypeRule.find(k)!=d_litTypeRule.end());
      Expr kt = d_litTypeRule[k];
      printSetLiteralTypeRule(k, kt);
      tsLitsIndex++;
    }
    Kind k = c.getKind();
    if (k==Kind::PROGRAM_CONST)
    {
      printProgram(c, cval);
    }
    else if (k==Kind::PROOF_RULE)
    {
      printRule(c);
    }
    else if (k==Kind::CONST)
    {
      printDeclaration(c);
    }
    else
    {
      EO_FATAL() << "Unknown kind: " << k;
    }
  }

  std::stringstream ssoe;
  ssoe << s_td_path << "plugins/desugar/trim_defs_gen.eo";
  std::cout << "Write trim-defs    " << ssoe.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << d_defs.str();
}


}  // namespace ethos
