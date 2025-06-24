/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "desugar.h"

#include "state.h"
#include <fstream>
#include <sstream>
#include <string>

namespace ethos {

std::string s_ds_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
//std::string s_ds_path = "/home/andrew/ethos/";

Desugar::Desugar(State& s) : d_state(s), d_tc(s.getTypeChecker()) {

}

Desugar::~Desugar() {}

void Desugar::initialize()
{
}

void Desugar::reset() {}

void Desugar::pushScope() {}

void Desugar::popScope() {}

void Desugar::includeFile(const Filepath& s, bool isReference, const Expr& referenceNf) {}

void Desugar::setLiteralTypeRule(Kind k, const Expr& t)
{
  d_declSeen.emplace_back(t, k);
}

void Desugar::finalizeSetLiteralTypeRule(Kind k, const Expr& t)
{
  std::stringstream ss;
  ss << "(declare-consts ";
  switch (k)
  {
    case Kind::NUMERAL: ss << "<numeral>"; break;
    case Kind::RATIONAL: ss << "<rational>"; break;
    case Kind::BINARY: ss << "<binary>"; break;
    case Kind::STRING: ss << "<string>"; break;
    case Kind::DECIMAL: ss << "<decimal>"; break;
    case Kind::HEXADECIMAL: ss << "<hexadecimal>"; break;
    default:
      EO_FATAL() << "Unknown literal type rule" << k << std::endl;
      break;
  }
  ss << " " << t << ")" << std::endl;
  // numeral is declared at the top
  if (k==Kind::NUMERAL)
  {
    Assert (t.getKind()==Kind::CONST);
    d_numDecl << "(declare-const " << t << " Type)" << std::endl;
    d_declProcessed.insert(t);
    d_numDecl << "; type-rules: " << k << std::endl;
    d_numDecl << ss.str();
    d_num << t;
  }
  else
  {
    d_defs << "; type-rules: " << k << std::endl;
    d_defs << ss.str();
  }
}

void Desugar::bind(const std::string& name, const Expr& e)
{
  Kind k = e.getKind();
  if (k==Kind::LAMBDA)
  {
    // remember the name
    Expr tmp = d_state.mkSymbol(Kind::CONST, name, d_state.mkAny());
    Expr p = d_state.mkPair(tmp, e);
    d_declSeen.emplace_back(p, Kind::LAMBDA);
  }
  else if (k==Kind::CONST || k==Kind::PROOF_RULE)
  {
    d_declSeen.emplace_back(e, k);
  }
}

void Desugar::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
 d_attrDecl[v] = std::pair<Attr, Expr>(a, cons);
}

void Desugar::markOracleCmd(const Expr& v, const std::string& ocmd) {}

void Desugar::defineProgram(const Expr& v, const Expr& prog)
{
  Expr pair = d_state.mkPair(v, prog);
  d_declSeen.emplace_back(pair, Kind::PROGRAM_CONST);
}

void Desugar::finalizeProgram(const Expr& e, const Expr& prog)
{
  Expr p = e;
  Expr pt = d_tc.getType(p);
  std::vector<Expr> pandt{pt, prog};
  std::vector<Expr> vars = Expr::getVariables(pandt);
  d_defs << "; " << (prog.isNull() ? "fwd-decl: " : "program: ") << e << std::endl;
  d_defs << "(program " << e << " (";
  std::vector<Expr> params;
  printParamList(vars, d_defs, params, false);
  d_defs << ")" << std::endl;
  Assert (pt.getKind()==Kind::PROGRAM_TYPE);
  Assert (pt.getNumChildren()>1);
  d_defs << "  :signature (";
  size_t pargs = pt.getNumChildren()-1;
  for (size_t i=0; i<pargs; i++)
  {
    if (i>0)
    {
      d_defs << " ";
    }
    d_defs << pt[i];
  }
  d_defs << ") ";
  d_defs << pt[pargs];
  d_defs << std::endl;
  if (!prog.isNull())
  {
    d_defs << "  (" << std::endl;
    for (size_t i=0, ncases = prog.getNumChildren(); i<ncases; i++)
    {
      const Expr& c = prog[i];
      d_defs << "  (" << c[0] << " " << c[1] << ")" << std::endl;
    }
    d_defs << "  )" << std::endl;
  }
  d_defs << ")" << std::endl;
}

void Desugar::finalizeDeclaration(const Expr& e)
{
  Expr c = e;
  Attr cattr = Attr::NONE;
  Expr cattrCons;
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  it = d_attrDecl.find(e);
  if (it!=d_attrDecl.end())
  {
    cattr = it->second.first;
    cattrCons = it->second.second;
  }
  if (cattr==Attr::DATATYPE || cattr==Attr::DATATYPE_CONSTRUCTOR || cattr==Attr::AMB_DATATYPE_CONSTRUCTOR)
  {
    // handled as part of datatype
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
  Expr ct = d_tc.getType(c);
  std::vector<Expr> argTypes;
  Expr retType;
  std::map<Expr, bool> visited;
  bool firstParam = true;
  std::vector<Expr> params;
  std::stringstream opaqueArgs;
  if (ct.getKind()==Kind::FUNCTION_TYPE)
  {
    if (cattr==Attr::OPAQUE)
    {
      size_t novars = ct.getNumChildren()-1;
      for (size_t i=0; i<novars; i++)
      {
        Assert (ct[i].getKind()==Kind::QUOTE_TYPE) << "Bad opaque function type " << ct << " for " << c;
        Expr v = ct[i][0];
        if (v.getKind()==Kind::ANNOT_PARAM)
        {
          v = v[0];
        }
        Assert (v.getKind()==Kind::PARAM) << "Bad opaque function variable " << ct << " for " << c;
        std::vector<Expr> vars;
        vars.push_back(v);
        printParamList(vars, opaqueArgs, params, true, visited, firstParam, true);
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
    d_defs << "parameterized-const " << e << " (" << opaqueArgs.str();
    size_t argTypeStart = 0;
    if (cattr==Attr::AMB)
    {
      // skip the first type
      argTypeStart = 1;
    }
    size_t pcount = 0;
    for (size_t i=argTypeStart, nargs=argTypes.size(); i<nargs; i++)
    {
      Expr at = argTypes[i];
      Kind ak = at.getKind();
      if (ak==Kind::QUOTE_TYPE)
      {
        Expr v = at[0];
        if (v.getKind()==Kind::ANNOT_PARAM)
        {
          v = v[0];
        }
        if (v.getKind()==Kind::PARAM)
        {
          std::vector<Expr> vars;
          vars.push_back(v);
          printParamList(vars, d_defs, params, true, visited, firstParam);
        }
        else
        {
          Assert (false) << "Non-param quote " << ct << " for " << c;
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
    d_defs << ") " << retType << ")" << std::endl;
  }
  else
  {
    d_defs << "const " << e << " " << ct << ")" << std::endl;
  }
  if (cattr==Attr::RIGHT_ASSOC_NIL || cattr==Attr::LEFT_ASSOC_NIL)
  {
    d_eoNil << "  (($eo_nil " << e << " T) ";
    std::vector<Expr> nvars = Expr::getVariables(cattrCons);
    // print the type
    if (!nvars.empty())
    {
      Assert(ct.getKind() == Kind::FUNCTION_TYPE);
      Assert (cattrCons.getKind() == Kind::PARAMETERIZED);
      cattrCons = cattrCons[1];
      // ensure the parameters in the type have been printed, which should
      // be a superset of those in cattrCons
      nvars = Expr::getVariables(ct[0]);
      std::stringstream ngnil;
      ngnil << "$eo_nil_" << e;
      std::string pname = ngnil.str();
      d_eoNilNground << "(program " << pname << " (($eo_T Type) ";
      std::vector<Expr> params;
      printParamList(nvars, d_eoNilNground, params, false);
      d_eoNilNground << ")" << std::endl;
      d_eoNilNground << "  :signature ((eo::quote $eo_T)) $eo_T" << std::endl;
      d_eoNilNground << "  (" << std::endl;
      d_eoNilNground << "  ((" << pname << " " << ct[0] << ") " << cattrCons << ")" << std::endl;
      d_eoNilNground << "  )" << std::endl;
      d_eoNilNground << ")" << std::endl;
      d_eoNil << "(" << pname << " T)";
    }
    else
    {
      d_eoNil << cattrCons;
    }
    d_eoNil << ")" << std::endl;
  }
}

void Desugar::printParamList(const std::vector<Expr>& vars, std::ostream& os, std::vector<Expr>& params, bool useImplicit)
{
  std::map<Expr, bool> visited;
  bool firstParam = true;
  printParamList(vars, os, params, useImplicit, visited, firstParam);
}

void Desugar::printParamList(const std::vector<Expr>& vars, std::ostream& os, std::vector<Expr>& params, bool useImplicit, std::map<Expr, bool>& visited, bool& firstParam, bool isOpaque)
{
  std::map<Expr, bool>::iterator itv;
  std::vector<Expr> toVisit(vars.begin(), vars.end());
  Expr cur;
  while (!toVisit.empty())
  {
    cur = toVisit.back();
    Assert (cur.getKind()==Kind::PARAM);
    itv = visited.find(cur);
    if (itv!=visited.end() && itv->second)
    {
      toVisit.pop_back();
      continue;
    }
    Expr tcur = d_tc.getType(cur);
    if (itv==visited.end())
    {
      visited[cur] = false;
      // ensure its type has been printed
      Assert (!tcur.isNull());
      std::vector<Expr> tvars = Expr::getVariables(tcur);
      toVisit.insert(toVisit.end(), tvars.begin(), tvars.end());
      continue;
    }
    else if (!itv->second)
    {
      Assert (!itv->second);
      visited[cur] = true;
      if (firstParam)
      {
        firstParam = false;
      }
      else
      {
        os << " ";
      }
      os << "(" << cur << " " << tcur;
      if (std::find(vars.begin(), vars.end(), cur)==vars.end())
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
  
void Desugar::finalizeDefinition(const std::string& name, const Expr& t)
{
  Assert (t.getKind()==Kind::LAMBDA);
  d_defs << "; define: " << name << std::endl;
  d_defs << "(define " << name << " (";
  std::vector<Expr> vars;
  for (size_t i=0, nvars=t[0].getNumChildren(); i<nvars; i++)
  {
    vars.push_back(t[0][i]);
  }
  std::vector<Expr> params;
  printParamList(vars, d_defs, params, true);
  d_defs << ")" << std::endl;
  d_defs << "  ";
  d_defs << t[1] << ")" << std::endl;
}

void Desugar::finalizeRule(const Expr& e)
{
  Expr r = e;
  Expr rto = d_tc.getType(r);

  // compile to Eunoia program
  std::vector<Expr> avars;
  Expr rt = mkRemoveAnnotParam(rto, avars);
  std::vector<Expr> vars = Expr::getVariables(rt);
  std::stringstream paramList;
  bool firstParam = true;
  std::map<Expr, bool> visited;
  std::map<Expr, bool>::iterator itv;
  std::vector<Expr> toVisit(vars.begin(), vars.end());
  Expr cur;
  std::stringstream tcrSig;
  std::stringstream tcrBody;
  std::stringstream tcrCall;
  // ethos ctx
  std::vector<Expr> keep;
  Ctx ectx;
  bool firstTc = true;
  std::vector<Expr> params;
  while (!toVisit.empty())
  {
    cur = toVisit.back();
    itv = visited.find(cur);
    if (itv!=visited.end() && itv->second)
    {
      toVisit.pop_back();
      continue;
    }
    Expr tcur = d_tc.getType(cur);
    if (itv==visited.end())
    {
      visited[cur] = false;
      // ensure its type has been printed
      Assert (!tcur.isNull());
      std::vector<Expr> tvars = Expr::getVariables(tcur);
      toVisit.insert(toVisit.end(), tvars.begin(), tvars.end());
      continue;
    }
    else if (!itv->second)
    {
      Assert (!itv->second);
      visited[cur] = true;
      if (firstParam)
      {
        firstParam = false;
      }
      else
      {
        paramList << " ";
      }
      std::stringstream cname;
      cname << cur;
      paramList << "(" << cname.str() << " " << tcur << ")";
      toVisit.pop_back();
      params.push_back(cur);
      // if an original variable
      if (std::find(vars.begin(), vars.end(), cur)!=vars.end())
      {
        // its type must match
        if (firstTc)
        {
          firstTc = false;
        }
        else
        {
          tcrSig << " ";
        }
        tcrSig << tcur << " Type";
        tcrBody << " " << cur << " " << tcur;
        tcrCall << " " << cur << " (eo::typeof " << cur << ")";
      }
    }
  }
  std::vector<bool> argIsProof;
  d_eoRules << "; rule: " << e << std::endl;
  if (rt.getKind()==Kind::FUNCTION_TYPE)
  {
    std::stringstream typeList;
    std::stringstream argList;
    for (size_t i=1, nargs = rt.getNumChildren(); i<nargs; i++)
    {
      if (i>1)
      {
        typeList << " ";
      }
      Expr argType = rt[i-1];
      Kind ak = argType.getKind();
      if (ak==Kind::QUOTE_TYPE || ak==Kind::PROOF_TYPE)
      {
        // handled the same: argument is first child
        Expr aa = argType[0];
        Expr ta = d_tc.getType(aa);
        bool isProof = (ak==Kind::PROOF_TYPE);
        if (isProof)
        {
          //typeList << "(! " << ta << " :premise)";
          typeList << ta;
        }
        else
        {
          typeList << ta;
        }
        argList << " " << argType[0];
        argIsProof.push_back(isProof);
      }
    }
    // strip off the "(Proof ...)", which may be beneath requires
    Expr rrt = rt[rt.getNumChildren()-1];
    std::vector<Expr> reqs;
    while (rrt.getKind()==Kind::EVAL_REQUIRES)
    {
      reqs.push_back(d_state.mkPair(rrt[0], rrt[1]));
      rrt = rrt[2];
    }
    Assert (rrt.getKind()==Kind::PROOF_TYPE);
    rrt = rrt[0];
    rrt = d_state.mkRequires(reqs, rrt);
    // just use the same parameter list
    d_eoRules << "(program $eor.exec_" << e << " (" << paramList.str() << ")" << std::endl;
    d_eoRules << "  :signature (" << tcrSig.str() << ") Bool" << std::endl;
    d_eoRules << "  (" << std::endl;
    d_eoRules << "  (($eor.exec_" << e << tcrBody.str() << ") " << rrt << ")" << std::endl;
    d_eoRules << "  )" << std::endl;
    d_eoRules << ")" << std::endl;
    d_eoRules << "(program $eor_" << e << " (" << paramList.str() << ")" << std::endl;
    d_eoRules << "  :signature (" << typeList.str() << ")";
    d_eoRules << " Bool" << std::endl;
    d_eoRules << "  (" << std::endl;
    d_eoRules << "  (($sm_" << e << argList.str() << ") ($eor.exec_" << e << tcrCall.str() << "))" << std::endl;
    d_eoRules << "  )" << std::endl;
    d_eoRules << ")" << std::endl;
    d_eoRules << std::endl;
  }
  else
  {
    // ground rule is just a formula definition
    Assert (rt.getKind()==Kind::PROOF_TYPE);
    Expr rrt = rt[0];
    d_eoRules << "(define $eor_" << e << " () " << rrt << ")" << std::endl << std::endl;
  }

}

void Desugar::finalize()
{
  for (std::pair<Expr, Kind>& d : d_declSeen)
  {
    Kind k = d.second;
    Expr e = d.first;
    if (d_declProcessed.find(e)!=d_declProcessed.end())
    {
      continue;
    }
    if (k==Kind::NUMERAL || k==Kind::RATIONAL || k==Kind::BINARY || k==Kind::STRING || k==Kind::DECIMAL || k==Kind::HEXADECIMAL)
    {
      // defines
      finalizeSetLiteralTypeRule(k, e);
    }
    else if (k==Kind::LAMBDA)
    {
      Assert (e.getNumChildren()==2);
      std::stringstream ss;
      ss << e[0];
      finalizeDefinition(ss.str(), e[1]);
    }
    else if (k==Kind::CONST)
    {
      finalizeDeclaration(e);
    }
    else if (k==Kind::PROOF_RULE)
    {
      finalizeRule(e);
    }
    else if (k==Kind::PROGRAM_CONST)
    {
      Assert (e.getNumChildren()==2);
      finalizeProgram(e[0], e[1]);
    }
    else
    {
      EO_FATAL() << "Unknown kind: " << k;
    }
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
  
  // now, go back and compile *.eo for the proof rules
  std::stringstream ssie;
  ssie << s_ds_path << "plugins/desugar/eo_desugar.eo";
  std::ifstream ine(ssie.str());
  std::ostringstream sse;
  sse << ine.rdbuf();
  std::string finalEo = sse.str();
  
  replace(finalEo, "$EO_NUMERAL_DECL$", d_numDecl.str());
  replace(finalEo, "$EO_NUMERAL$", d_num.str());
  replace(finalEo, "$EO_DEFS$", d_defs.str());
  replace(finalEo, "$EO_NIL_CASES$", d_eoNil.str());
  replace(finalEo, "$EO_NIL_NGROUND_DEFS$", d_eoNilNground.str());
  replace(finalEo, "$EO_TYPEOF_CASES$", d_eoTypeof.d_out.str());
  replace(finalEo, "$EO_TYPEOF_PARAM$", d_eoTypeof.d_param.str());
  replace(finalEo, "$EO_DT_CONSTRUCTORS_CASES$", d_eoDtCons.d_out.str());
  replace(finalEo, "$EO_DT_CONSTRUCTORS_PARAM$", d_eoDtCons.d_param.str());
  replace(finalEo, "$EO_DT_SELECTORS_CASES$", d_eoDtSel.d_out.str());
  replace(finalEo, "$EO_DT_SELECTORS_PARAM$", d_eoDtSel.d_param.str());
  replace(finalEo, "$EO_RULES$", d_eoRules.str());
  
  std::stringstream ssoe;
  ssoe << s_ds_path << "plugins/desugar/eo_desugar_gen.eo";
  std::ofstream oute(ssoe.str());
  oute << finalEo;
}


bool Desugar::hasSubterm(const Expr& t, const Expr& s)
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
    if (cur==s)
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

Expr Desugar::mkRemoveAnnotParam(const Expr& t, std::vector<Expr>& vars)
{
  std::unordered_map<const ExprValue*, Expr> visited;
  std::unordered_map<const ExprValue*, Expr>::iterator it;
  std::vector<Expr> visit;
  Expr cur;
  visit.push_back(t);
  do
  {
    cur = visit.back();
    it = visited.find(cur.getValue());
    if (it == visited.end())
    {
      visited[cur.getValue()] = d_null;
      for (size_t i=0, nchild=cur.getNumChildren(); i<nchild; i++)
      {
        visit.push_back(cur[i]);
      }
      continue;
    }
    visit.pop_back();
    if (it->second.isNull())
    {
      Expr ret = cur;
      bool childChanged = false;
      std::vector<Expr> children;
      for (size_t i=0, nchild=cur.getNumChildren(); i<nchild; i++)
      {
        Expr cn = cur[i];
        it = visited.find(cn.getValue());
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      Kind k = cur.getKind();
      if (k==Kind::ANNOT_PARAM)
      {
        // strip off the "(eo::param ...)"
        vars.push_back(cur);
        ret = cur[0];
      }
      else if (childChanged)
      {
        ret = Expr(d_state.mkExprSimple(k, children));
      }
      visited[cur.getValue()] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(t.getValue()) != visited.end());
  Assert(!visited.find(t.getValue())->second.isNull());
  return visited[t.getValue()];
}

}  // namespace ethos
