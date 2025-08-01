/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "desugar.h"

#include <fstream>
#include <sstream>
#include <string>

#include "../flatten_eval/flatten_eval.h"
#include "state.h"

namespace ethos {

Desugar::Desugar(State& s) : StdPlugin(s)
{
  // we require santization of the eo::List at this stage
  // TODO: maybe just use text replace??
  d_listNil = s.mkListNil();
  Expr lnt = d_tc.getType(d_listNil);
  d_overloadSanVisited[d_listNil] =
      d_state.mkSymbol(Kind::CONST, "$eo_List_nil", lnt);
  d_listCons = s.mkListCons();
  Expr lct = d_tc.getType(d_listCons);
  d_overloadSanVisited[d_listCons] =
      d_state.mkSymbol(Kind::CONST, "$eo_List_cons", lct);
  d_listType = s.mkListType();
  Expr lt = d_tc.getType(d_listType);
  d_overloadSanVisited[d_listType] =
      d_state.mkSymbol(Kind::CONST, "$eo_List", lt);
  d_genVcs = d_state.getOptions().d_pluginDesugarGenVc;
  if (d_genVcs)
  {
    d_eoVc << ";; verification conditions" << std::endl << std::endl;
  }
  d_eoDtConsParamCount = 0;
  d_genWfCond = false;

  // a placeholder
  d_boolType = d_state.mkBoolType();
  Expr ttype = d_state.mkType();
  Expr optBoolType = d_state.mkSymbol(Kind::CONST, "$eo_Option", ttype);
  Expr modelSatType = d_state.mkProgramType({d_boolType}, optBoolType);
  d_peoModelSat =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_model_sat", modelSatType);
  Expr modelTypeofType = d_state.mkProgramType({d_boolType}, ttype);
  d_peoModelTypeof =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_typeof", modelTypeofType);
  Expr modelIsInputType = d_state.mkProgramType({d_boolType}, d_boolType);
  d_peoModelIsInput = d_state.mkSymbol(
      Kind::PROGRAM_CONST, "$eo_model_is_input", modelIsInputType);
  Expr anyT = allocateTypeVariable();
  Expr anyT2 = allocateTypeVariable();
  Expr eoRequireEqType = d_state.mkProgramType({anyT, anyT, anyT2}, anyT2);
  d_peoRequiresEq =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_requires_eq", eoRequireEqType);
  d_peoRequiresDeq = d_state.mkSymbol(
      Kind::PROGRAM_CONST, "$eo_requires_deq", eoRequireEqType);
  Expr optSomeType = d_state.mkProgramType({d_boolType}, d_listType);
  d_peoOptionSome =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_Option_some", optSomeType);
}

Desugar::~Desugar() {}

void Desugar::bind(const std::string& name, const Expr& e)
{
  Kind k = e.getKind();
  if (k == Kind::LAMBDA)
  {
    // We preserve macros in this stage
    // remember the name
    Expr tmp = d_state.mkSymbol(Kind::CONST, name, d_state.mkAny());
    Expr p = d_state.mkPair(tmp, e);
    d_declSeen.emplace_back(p, Kind::LAMBDA);
  }
  else if (k == Kind::CONST || k == Kind::PROOF_RULE)
  {
    d_declSeen.emplace_back(e, k);
  }
}

void Desugar::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  d_attrDecl[v] = std::pair<Attr, Expr>(a, cons);
}
void Desugar::defineProgram(const Expr& v, const Expr& prog)
{
  Expr pair = d_state.mkPair(v, prog);
  d_declSeen.emplace_back(pair, Kind::PROGRAM_CONST);
}

void Desugar::finalizeProgram(const Expr& prog,
                              const Expr& progDef,
                              std::ostream& os)
{
  std::map<Expr, Expr> typeMap;
  std::vector<std::pair<Expr, Expr>> allDefs;
  if (StdPlugin::optionFlattenEval())
  {
    allDefs = FlattenEval::flattenProgram(d_state, prog, progDef, typeMap);
  }
  else
  {
    allDefs.emplace_back(prog, progDef);
  }
  for (std::pair<Expr, Expr>& d : allDefs)
  {
    Expr p = d.first;
    Expr pdef = d.second;
    Expr pt = d_tc.getType(p);
    std::vector<Expr> pandt{pt, pdef};
    std::vector<Expr> vars = Expr::getVariables(pandt);
    os << "; " << (pdef.isNull() ? "fwd-decl: " : "program: ") << p
       << std::endl;
    os << "(program " << p << " (";
    printParamList(vars, os, false);
    os << ")" << std::endl;
    Assert(pt.getKind() == Kind::PROGRAM_TYPE);
    Assert(pt.getNumChildren() > 1);
    os << "  :signature (";
    size_t pargs = pt.getNumChildren() - 1;
    for (size_t i = 0; i < pargs; i++)
    {
      if (i > 0)
      {
        os << " ";
      }
      Expr ptip = typeMap[pt[i]];
      ptip = ptip.isNull() ? pt[i] : ptip;
      printTerm(ptip, os);
    }
    os << ") ";
    Expr ptrp = typeMap[pt[pargs]];
    ptrp = ptrp.isNull() ? pt[pargs] : ptrp;
    printTerm(ptrp, os);
    os << std::endl;
    if (!pdef.isNull())
    {
      os << "  (" << std::endl;
      for (size_t i = 0, ncases = pdef.getNumChildren(); i < ncases; i++)
      {
        const Expr& c = pdef[i];
        os << "  (";
        printTerm(c[0], os);
        os << " ";
        printTerm(c[1], os);
        os << ")" << std::endl;
      }
      os << "  )" << std::endl;
    }
    os << ")" << std::endl;
  }
}

void Desugar::finalizeDeclaration(const Expr& e, std::ostream& os)
{
  if (d_declProcessed.find(e) != d_declProcessed.end())
  {
    // handles the case where declaration is handled separately e.g. Int
    return;
  }
  d_declProcessed.insert(e);
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
  if (cattr == Attr::DATATYPE || cattr == Attr::DATATYPE_CONSTRUCTOR
      || cattr == Attr::AMB_DATATYPE_CONSTRUCTOR)
  {
    finalizeDatatype(e, cattr, cattrCons);
    // also handle it as a normal declaration below
  }
  bool isAmb = (cattr == Attr::AMB || cattr == Attr::AMB_DATATYPE_CONSTRUCTOR);
  bool hasOpaqueArg = (cattr == Attr::OPAQUE || isAmb);
  // check for eo::List
  std::stringstream cnss;
  printName(c, cnss);
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
        printParamList(vars, opaqueArgs, params, visited, true, true);
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
  os << "; declare: " << e << std::endl;
  os << "(declare-";
  std::vector<Expr> vars = Expr::getVariables(ct);
  if (!vars.empty())
  {
    os << "parameterized-const " << cname << " (" << opaqueArgs.str();
    size_t pcount = 0;
    for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
    {
      Expr at = argTypes[i];
      if (at.getKind() == Kind::QUOTE_TYPE)
      {
        Expr v = at[0];
        if (v.getKind() == Kind::ANNOT_PARAM)
        {
          v = v[0];
        }
        if (v.getKind() == Kind::PARAM)
        {
          std::vector<Expr> varsp;
          varsp.push_back(v);
          printParamList(varsp, os, params, visited, true);
        }
        else if (isAmb && i == 0)
        {
          // skip, the remaining free variables will be printed as implicit
          // below.
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
        printParamList(vars, os, params, visited, true);
      }
    }
    // if ambiguous, go back and print the remaining parameters as implicit
    if (isAmb)
    {
      Assert(argTypes[0].getKind() == Kind::QUOTE_TYPE);
      Expr v = argTypes[0][0];
      // print the parameters; these will lead to a definition that is
      // ambiguous again.
      std::vector<Expr> avars = Expr::getVariables(v);
      // override the behavior to ensure all variables are implicit.
      size_t startIndex = params.size();
      getParamList(avars, params, visited);
      std::vector<Expr> emptyVec;
      finalizeParamList(os, params, true, emptyVec, false, startIndex);
    }
    os << ") ";
    printTerm(retType, os);
  }
  else
  {
    os << "const " << cname << " ";
    printTerm(ct, os);
  }
  // TODO: is this necessary?
  // carry the marked semantics
  std::map<Expr, Expr>::iterator itm = d_markedSemantics.find(e);
  if (itm != d_markedSemantics.end())
  {
    os << " :semantics ";
    printTerm(itm->second, os);
  }
  os << ")" << std::endl;
  d_declProcessed.insert(e);
  // handle eo_nil
  if (cattr == Attr::RIGHT_ASSOC_NIL || cattr == Attr::LEFT_ASSOC_NIL)
  {
    d_eoNil << "  (($eo_nil " << e << " T) ";
    std::vector<Expr> nvars = Expr::getVariables(cattrCons);
    // print the type
    if (!nvars.empty())
    {
      Assert(ct.getKind() == Kind::FUNCTION_TYPE);
      Assert(cattrCons.getKind() == Kind::PARAMETERIZED);
      cattrCons = cattrCons[1];
      // ensure the parameters in the type have been printed, which should
      // be a superset of those in cattrCons
      nvars = Expr::getVariables(ct[0]);
      std::stringstream ngnil;
      ngnil << "$eo_nil_";
      printName(e, ngnil);
      std::string pname = ngnil.str();
      Expr tpTmp = allocateTypeVariable();
      Expr qtt = d_state.mkExpr(Kind::QUOTE_TYPE, {tpTmp});
      Expr progType = d_state.mkProgramType({qtt}, tpTmp);
      Expr prog = d_state.mkSymbol(Kind::PROGRAM_CONST, pname, progType);
      Expr progPat = d_state.mkExpr(Kind::APPLY, {prog, ct[0]});
      Expr progPair = d_state.mkPair(progPat, cattrCons);
      Expr progDef = d_state.mkExpr(Kind::PROGRAM, {progPair});
      finalizeProgram(prog, progDef, d_eoNilNground);
      d_eoNil << "(" << pname << " T)";
    }
    else
    {
      d_eoNil << cattrCons;
    }
    d_eoNil << ")" << std::endl;
  }
  // handle eo_typeof
  ct = cto;
  d_eoTypeof << "  ; type-rule: " << e << std::endl;
  // good for debugging
  // d_eoTypeof << "  ; type is " << ct << std::endl;
  if (!ct.isGround())
  {
    Assert(ct.getKind() == Kind::FUNCTION_TYPE)
        << "Not function type " << ct << " for " << e;
    // std::cout << "Non-ground function type: " << e << " : " << ct <<
    // std::endl; std::cout << "Attribute is " << attr << std::endl;
    //  We traverse to a position where the type of a partial application
    //  of this operator has ground type.
    Expr pattern = e;
    std::vector<Expr> argTypes;
    std::vector<Expr> allVars = Expr::getVariables(ct);
    std::stringstream sslc;
    std::stringstream sslcEnd;
    size_t ngArgs = 0;
    std::stringstream ssngarg;
    std::vector<Expr> ngscope;
    size_t argCount = 0;
    while (ct.getKind() == Kind::FUNCTION_TYPE)
    {
      std::vector<Expr> args;
      args.push_back(pattern);
      size_t nargs = ct.getNumChildren();
      for (size_t i = 1; i < nargs; i++)
      {
        Expr cta = ct[i - 1];
        std::stringstream ssx;
        argCount++;
        ssx << "x" << argCount;
        Expr arg;
        if (cta.getKind() == Kind::QUOTE_TYPE)
        {
          cta = cta[0];
          if (cta.getKind() == Kind::ANNOT_PARAM)
          {
            ngscope.push_back(cta[1]);
            ssngarg << " ($eo_typeof " << ssx.str() << ")";
            cta = cta[0];
          }
          Expr tcta = d_tc.getType(cta);
          arg = d_state.mkSymbol(Kind::PARAM, ssx.str(), tcta);
          if (cta.getKind() == Kind::PARAM)
          {
            sslc << "(eo::define ((" << cta << " " << arg << ")) ";
            sslcEnd << ")";
          }
          ssngarg << " " << arg;
        }
        else
        {
          arg = d_state.mkSymbol(Kind::PARAM, ssx.str(), cta);
          if (cta.isGround())
          {
            sslc << "($eo_requires_true ($eo_eq ($eo_typeof " << arg << ") ";
            printTerm(cta, sslc);
            sslc << ") ";
            sslcEnd << ")";
          }
          else if (cta.getKind() == Kind::PARAM)
          {
            sslc << "(eo::define ((" << cta << " ($eo_typeof " << arg << "))) ";
            sslcEnd << ")";
          }
          ssngarg << " ($eo_typeof " << arg << ")";
        }
        ngscope.push_back(cta);
        ngArgs++;
        args.push_back(arg);
        argTypes.push_back(cta);
      }
      Kind ak =
          (hasOpaqueArg && pattern == e) ? Kind::APPLY_OPAQUE : Kind::APPLY;
      pattern = d_state.mkExprSimple(ak, args);
      // std::cout << "...pattern is now " << pattern << " from " << args <<
      // std::endl;
      ct = ct[nargs - 1];
      // maybe we are now fully bound?
      std::vector<Expr> vars = Expr::getVariables(argTypes);
      if (allVars.size() == vars.size())
      {
        break;
      }
    }
    // should be implied
    // ngscope.push_back(ct);
    // std::cout << "Partial app that has ground type: " << pattern <<
    // std::endl;
    // we now write the pattern matching for the derived pattern.
    d_eoTypeof << "  (($eo_typeof_main ";
    printTerm(pattern, d_eoTypeof);
    d_eoTypeof << ") ";
    if (ngArgs > 0)
    {
      std::stringstream ssng;
      ssng << "$eo_typeof_";
      printName(e, ssng);
      std::string pname = ssng.str();
      // construct the program and print it
      std::vector<Expr> argTypes;
      Expr retType = d_state.mkType();
      for (size_t i = 0, ngsize = ngscope.size(); i < ngsize; i++)
      {
        argTypes.push_back(retType);
      }
      Expr progType = d_state.mkProgramType(argTypes, retType);
      Expr prog = d_state.mkSymbol(Kind::PROGRAM_CONST, pname, progType);
      std::vector<Expr> pchildren;
      pchildren.push_back(prog);
      pchildren.insert(pchildren.end(), ngscope.begin(), ngscope.end());
      Expr progPat = d_state.mkExpr(Kind::APPLY, pchildren);
      Expr progPair = d_state.mkPair(progPat, ct);
      Expr progDef = d_state.mkExpr(Kind::PROGRAM, {progPair});
      finalizeProgram(prog, progDef, d_eoTypeofNGround);
      d_eoTypeof << "(" << pname << ssngarg.str() << ")";
    }
    else
    {
      d_eoTypeof << sslc.str();
      printTerm(ct, d_eoTypeof);
      d_eoTypeof << sslcEnd.str();
    }
    d_eoTypeof << ")" << std::endl;
  }
  else
  {
    d_eoTypeof << "  (($eo_typeof_main " << e << ") ";
    printTerm(ct, d_eoTypeof);
    d_eoTypeof << ")" << std::endl;
  }
}

void Desugar::printName(const Expr& e, std::ostream& os)
{
  std::map<Expr, size_t>::iterator it = d_overloadId.find(e);
  size_t oid;
  if (it == d_overloadId.end())
  {
    std::stringstream ss;
    ss << e;
    std::string s = ss.str();
    oid = d_overloadCount[s];
    d_overloadId[e] = oid;
    d_overloadCount[s]++;
    if (oid > 0)
    {
      std::stringstream ss;
      ss << "$eoo_" << e << "." << (oid + 1);
      Expr c = e;
      Expr ct = d_tc.getType(c);
      Expr ctov = d_state.mkSymbol(e.getKind(), ss.str(), e);
      d_overloadSanVisited[e] = ctov;
    }
  }
  else
  {
    oid = it->second;
  }
  if (oid > 0)
  {
    os << "$eoo_" << e << "." << (oid + 1);
  }
  else
  {
    os << e;
  }
}

void Desugar::printTerm(const Expr& e, std::ostream& os)
{
  Expr es = mkSanitize(e);
  os << es;
}

void Desugar::printParamList(const std::vector<Expr>& vars,
                             std::ostream& os,
                             bool useImplicit,
                             bool isOpaque)
{
  std::vector<Expr> params;
  std::map<Expr, bool> visited;
  printParamList(vars, os, params, visited, useImplicit, isOpaque);
}

void Desugar::printParamList(const std::vector<Expr>& vars,
                             std::ostream& os,
                             std::vector<Expr>& params,
                             std::map<Expr, bool>& visited,
                             bool useImplicit,
                             bool isOpaque)
{
  size_t startIndex = params.size();
  // get the parameter list
  getParamList(vars, params, visited);
  // print it on the output stream
  finalizeParamList(os, params, useImplicit, vars, isOpaque, startIndex);
}

void Desugar::getParamList(const std::vector<Expr>& vars,
                           std::vector<Expr>& params,
                           std::map<Expr, bool>& visited)
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
      // ensure the variables in its type has been printed
      Assert(!tcur.isNull());
      std::vector<Expr> tvars = Expr::getVariables(tcur);
      toVisit.insert(toVisit.end(), tvars.begin(), tvars.end());
      continue;
    }
    else if (!itv->second)
    {
      Assert(!itv->second);
      visited[cur] = true;
      params.emplace_back(cur);
      toVisit.pop_back();
    }
  }
}

void Desugar::finalizeParamList(std::ostream& os,
                                const std::vector<Expr>& params,
                                bool useImplicit,
                                const std::vector<Expr>& nimplicit,
                                bool isOpaque,
                                size_t startIndex)
{
  for (size_t i = startIndex, nparams = params.size(); i < nparams; i++)
  {
    if (i > 0)
    {
      os << " ";
    }
    Expr cur = params[i];
    os << "(" << cur << " ";
    Expr tcur = d_tc.getType(cur);
    printTerm(tcur, os);
    if (std::find(nimplicit.begin(), nimplicit.end(), cur) == nimplicit.end())
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
  }
}

void Desugar::finalizeDefinition(const std::string& name, const Expr& t)
{
  return;
  Assert(t.getKind() == Kind::LAMBDA);
  d_defs << "; define: " << name << std::endl;
  d_defs << "(define " << name << " (";
  std::vector<Expr> vars;
  for (size_t i = 0, nvars = t[0].getNumChildren(); i < nvars; i++)
  {
    vars.push_back(t[0][i]);
  }
  printParamList(vars, d_defs, true);
  d_defs << ")" << std::endl;
  d_defs << "  ";
  printTerm(t[1], d_defs);
  d_defs << ")" << std::endl;
}

void Desugar::finalizeRule(const Expr& e)
{
  // std::cout << "Finalize rule " << e << std::endl;
  Expr r = e;
  Expr rto = d_tc.getType(r);
  Expr rt = mkSanitize(rto);
  // Make program
  std::vector<bool> argIsProof;
  std::vector<Expr> args;
  std::vector<Expr> argsS;
  std::vector<Expr> argsTypes;
  Expr etrue = d_state.mkTrue();
  Expr efalse = d_state.mkFalse();
  // accumulated requirements for returned conclusion
  std::vector<Expr> reqs;
  Expr rrt;
  if (rt.getKind() != Kind::FUNCTION_TYPE)
  {
    Expr dummy = d_state.mkSymbol(Kind::PARAM, "$etmp", d_boolType);
    // dummy argument
    argIsProof.push_back(false);
    args.push_back(dummy);
    argsS.push_back(dummy);
    argsTypes.push_back(d_state.mkBoolType());
    rrt = rt;
  }
  else
  {
    std::map<Expr, Expr> evMap = d_overloadSanVisited;
    size_t eVarCount = 0;
    std::vector<std::pair<Expr, Expr>> newVars;
    for (size_t i = 1, nargs = rt.getNumChildren(); i < nargs; i++)
    {
      Expr arg = rt[i - 1];
      Expr argS = mkSanitize(arg, evMap, eVarCount, true, newVars);
      Kind ak = argS.getKind();
      if (ak == Kind::QUOTE_TYPE || ak == Kind::PROOF_TYPE)
      {
        Assert(arg.getKind() == argS.getKind());
        Expr aa = argS[0];
        Expr ta = d_tc.getType(aa);
        if (ta.isNull() || ta.isEvaluatable())
        {
          // EO_FATAL() << "Could not get type of " << aa << std::endl;
          ta = allocateTypeVariable();
        }
        argIsProof.push_back(ak == Kind::PROOF_TYPE);
        args.push_back(arg[0]);
        argsS.push_back(argS[0]);
        argsTypes.push_back(ta);
      }
      else
      {
        Assert(false) << "Unknown proof argument " << ak << " in " << rt;
      }
    }
    // we addtionally require that the purified variables are equal to what the
    // purify
    for (std::pair<Expr, Expr>& nv : newVars)
    {
      reqs.push_back(d_state.mkPair(nv.first, nv.second));
    }
    rrt = rt[rt.getNumChildren() - 1];
  }
  // strip off the "(Proof ...)", which may be beneath requires
  while (rrt.getKind() == Kind::EVAL_REQUIRES)
  {
    reqs.push_back(d_state.mkPair(rrt[0], rrt[1]));
    rrt = rrt[2];
  }
  Assert(rrt.getKind() == Kind::PROOF_TYPE)
      << "Bad return type: " << rrt.getKind() << " " << rrt;
  rrt = rrt[0];
  if (StdPlugin::optionVcUseTypeof())
  {
    // the final conclusion must have Bool type
    rrt = mkRequiresModelTypeofBool(rrt, rrt);
  }
  rrt = d_state.mkRequires(reqs, rrt);

  Expr progType = d_state.mkProgramType(argsTypes, d_boolType);
  std::stringstream pname;
  pname << "$eor_" << e;
  Expr prog = d_state.mkSymbol(Kind::PROGRAM_CONST, pname.str(), progType);
  Expr progApps[2];
  for (size_t i = 0; i < 2; i++)
  {
    std::vector<Expr>& ause = (i == 0 ? argsS : args);
    std::vector<Expr> pAppChildren;
    pAppChildren.push_back(prog);
    pAppChildren.insert(pAppChildren.end(), ause.begin(), ause.end());
    progApps[i] = d_state.mkExpr(Kind::APPLY, pAppChildren);
  }
  Expr progPair = d_state.mkPair(progApps[0], rrt);
  Expr progDef = d_state.mkExpr(Kind::PROGRAM, {progPair});
  finalizeProgram(prog, progDef, d_eoVc);

  // if marked sorry, we should never do verification
  if (d_state.isProofRuleSorry(e.getValue()))
  {
    return;
  }

  Expr conclusion = progApps[1];
  std::stringstream pvcname;
  pvcname << "$eovc_" << e;
  Expr unsound = etrue;
  // require that the conclusion is not satisfied
  unsound = mkRequiresModelSat(false, conclusion, unsound);
  // require that each premise is satisfied
  for (size_t i = 0, nargs = args.size(); i < nargs; i++)
  {
    size_t ii = nargs - (i + 1);
    if (argIsProof[ii])
    {
      unsound = mkRequiresModelSat(true, args[ii], unsound);
      if (StdPlugin::optionVcUseTypeof())
      {
        unsound = mkRequiresModelTypeofBool(args[ii], unsound);
      }
    }
  }
  if (StdPlugin::optionVcUseIsInput())
  {
    // require that conclusion is an SMT-LIB term
    unsound = mkRequiresModelIsInput(conclusion, unsound);
  }
  std::vector<Expr> uvars = Expr::getVariables(unsound);
  if (uvars.empty())
  {
    // add a dummy variable
    Expr dummy = d_state.mkSymbol(Kind::PARAM, "$etmp", d_boolType);
    uvars.push_back(dummy);
  }
  std::vector<Expr> uargTypes;
  for (const Expr& v : uvars)
  {
    Expr vv = v;
    uargTypes.push_back(d_tc.getType(vv));
    if (StdPlugin::optionVcUseArgIsInput())
    {
      unsound = mkRequiresModelIsInput(vv, unsound);
    }
  }
  progType = d_state.mkProgramType(uargTypes, d_boolType);
  prog = d_state.mkSymbol(Kind::PROGRAM_CONST, pvcname.str(), progType);
  std::vector<Expr> vcpChildren;
  vcpChildren.push_back(prog);
  vcpChildren.insert(vcpChildren.end(), uvars.begin(), uvars.end());
  Expr progPat = d_state.mkExpr(Kind::APPLY, vcpChildren);
  progPair = d_state.mkPair(progPat, unsound);
  progDef = d_state.mkExpr(Kind::PROGRAM, {progPair});
  finalizeProgram(prog, progDef, d_eoVc);
  // write a command to indicate that we should process the above vc
  // we hard-code the symbols that are used in smt_meta.smt2 here.
  std::stringstream metaDeps;
  metaDeps << "$smtx_hash $eo_reverse_hash $smtx_value_hash "
              "$smtx_reverse_value_hash "
              "$eo_smt_type $tsm_Bool $eo_Type $eo_fun_type $eo_apply ";
  d_eoVc << "(echo \"smt-meta $eovc_" << e << " :deps " << metaDeps.str()
         << "\")" << std::endl;
}

void Desugar::finalizeDatatype(const Expr& e, Attr a, const Expr& attrCons)
{
  Assert(!attrCons.isNull());
  Expr d = e;
  Expr td = d_tc.getType(d);
  std::stringstream& os = a == Attr::DATATYPE ? d_eoDtCons : d_eoDtSel;
  std::string name = a == Attr::DATATYPE ? "constructors" : "selectors";
  os << "  (($eo_dt_" << name << " ";
  if (a == Attr::DATATYPE && td.getKind() == Kind::FUNCTION_TYPE)
  {
    os << "(";
    // parametric datatypes
    os << e;
    size_t i = 1;
    std::stringstream argList;
    while (td.getKind() == Kind::FUNCTION_TYPE)
    {
      if (i > d_eoDtConsParamCount)
      {
        d_eoDtConsParam << " (W" << i << " Type)";
        d_eoDtConsParamCount++;
      }
      Assert(td.getNumChildren() == 2);
      argList << " W" << i;
      td = td[1];
      i++;
    }
    os << argList.str() << "))";
    // its constructor list must take into account AMB_DATATYPE_CONSTRUCTOR.
    Expr ac = attrCons;
    // should always have at least one constructor
    Assert(ac.getKind() == Kind::APPLY);
    std::stringstream osEnd;
    while (ac.getKind() == Kind::APPLY)
    {
      os << " (_ ($eo_List_cons ";
      Assert(ac[0].getKind() == Kind::APPLY);
      Expr cc = ac[0][1];
      // should be a constructor
      Attr cca = getAttribute(cc);
      if (cca == Attr::AMB_DATATYPE_CONSTRUCTOR)
      {
        os << "(" << cc << argList.str() << ")";
      }
      else
      {
        Assert(cca == Attr::DATATYPE_CONSTRUCTOR);
        os << cc;
      }
      os << ")";
      osEnd << ")";
      ac = ac[1];
    }
    os << osEnd.str() << ")" << std::endl;
    return;
  }
  else
  {
    // note that AMB_DATATYPE_CONSTRUCTOR does not impact this.
    os << e;
  }
  os << ") ";
  printTerm(attrCons, os);
  os << ")" << std::endl;
}

void Desugar::finalize()
{
  for (std::pair<Expr, Kind>& d : d_declSeen)
  {
    Kind k = d.second;
    Expr e = d.first;
    if (k == Kind::LAMBDA)
    {
      Assert(e.getNumChildren() == 2);
      std::stringstream ss;
      ss << e[0];
      finalizeDefinition(ss.str(), e[1]);
    }
    else if (k == Kind::CONST)
    {
      finalizeDeclaration(e, d_defs);
    }
    else if (k == Kind::PROOF_RULE)
    {
      finalizeRule(e);
    }
    else if (k == Kind::PROGRAM_CONST)
    {
      Assert(e.getNumChildren() == 2);
      finalizeProgram(e[0], e[1], d_defs);
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
  ssie << s_plugin_path << "plugins/desugar/eo_desugar.eo";
  std::ifstream ine(ssie.str());
  std::ostringstream sse;
  sse << ine.rdbuf();
  std::string finalEo = sse.str();

  replace(finalEo, "$EO_LITERAL_TYPE_DECL$", d_litTypeDecl.str());
  replace(finalEo, "$EO_LIT_TYPEOF_DEFS$", d_litTypeProg.str());
  replace(finalEo, "$EO_DEFS$", d_defs.str());
  replace(finalEo, "$EO_NIL_CASES$", d_eoNil.str());
  replace(finalEo, "$EO_NIL_NGROUND_DEFS$", d_eoNilNground.str());
  replace(finalEo, "$EO_TYPEOF_CASES$", d_eoTypeof.str());
  replace(finalEo, "$EO_TYPEOF_NGROUND_DEFS$", d_eoTypeofNGround.str());
  replace(finalEo, "$EO_DT_CONSTRUCTORS_PARAM$", d_eoDtConsParam.str());
  replace(finalEo, "$EO_DT_CONSTRUCTORS_CASES$", d_eoDtCons.str());
  replace(finalEo, "$EO_DT_SELECTORS_CASES$", d_eoDtSel.str());
  if (d_genVcs)
  {
    if (d_genWfCond)
    {
      finalizeWellFounded();
      replace(finalEo, "$EO_VC$", d_eoVcWf.str());
    }
    else
    {
      // Verification conditions for *all* proof rules are ready now
      // TODO: make this manual?
      replace(finalEo, "$EO_VC$", d_eoVc.str());
    }
  }
  else
  {
    replace(finalEo, "$EO_VC$", "");
  }
  std::stringstream ssoe;
  ssoe << s_plugin_path << "plugins/desugar/eo_desugar_gen.eo";
  std::cout << "Write core-defs    " << ssoe.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << finalEo;
}

void Desugar::finalizeWellFounded()
{
  // TODO
  // std::stringstream wfDefs;
  // generate well-foundedness method
  // size_t pcIdCount = 0;
  // std::map<Expr, size_t> pcId;
  // std::stringstream os;
  // os << "(declare-const @pcall (-> $eo_Numeral $eo_List Type))" << std::endl;
  // os << "(program $eovcwf_rec ((pc $eo_Numeral))" << std::endl;
  // os << "  :signature ($eo_Numeral $eo_List $eo_List) Bool" << std::endl;
  // os << "  (" << std::endl;
  // os << "  )" << std::endl;
  // os << ")" << std::endl;
}

bool Desugar::echo(const std::string& msg)
{
  if (msg == "desugar-wf")
  {
    d_genWfCond = true;
    return false;
  }
  return true;
}

Expr Desugar::mkSanitize(const Expr& t)
{
  // take overloads into account
  std::map<Expr, Expr> visited = d_overloadSanVisited;
  size_t varCount = 0;
  std::vector<std::pair<Expr, Expr>> newVars;
  return mkSanitize(t, visited, varCount, false, newVars);
}

bool isEvalApp(const Expr& cur)
{
  Kind k = cur.getKind();
  return isLiteralOp(k)
         || (k == Kind::APPLY && cur[0].getKind() == Kind::PROGRAM_CONST);
}

Expr Desugar::mkSanitize(const Expr& t,
                         std::map<Expr, Expr>& visited,
                         size_t& varCount,
                         bool inPatMatch,
                         std::vector<std::pair<Expr, Expr>>& newVars)
{
  std::map<Expr, Expr>::iterator it;
  std::vector<Expr> visit;
  Expr cur;
  visit.push_back(t);
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    Kind k = cur.getKind();
    if (it == visited.end())
    {
      // If we are sanitizing a pattern, in rare cases, that pattern
      // may have evaluation. This is e.g. the case for the premises
      // of RARE rules that contain list variables. In this mode,
      // if we are a top-level application of evaluation, we purify
      // this occurrence. We sanitize separately, not in pattern
      // matching mode.
      if (inPatMatch && isEvalApp(cur))
      {
        varCount++;
        Expr ret = mkSanitize(cur);
        std::stringstream ssv;
        ssv << "$ex_" << varCount;
        Expr tv = d_tc.getType(cur);
        if (tv.isNull() || tv.isEvaluatable())
        {
          tv = allocateTypeVariable();
        }
        Expr v = d_state.mkSymbol(Kind::PARAM, ssv.str(), tv);
        newVars.emplace_back(v, ret);
        visited[cur] = v;
        visit.pop_back();
      }
      else
      {
        visited[cur] = d_null;
        for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
        {
          visit.push_back(cur[i]);
        }
      }
      continue;
    }
    visit.pop_back();
    if (it->second.isNull())
    {
      Expr ret = cur;
      bool childChanged = false;
      std::vector<Expr> children;
      for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
      {
        Expr cn = cur[i];
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      // must introduce new parameter if matching a literal op kind
      if (k == Kind::ANNOT_PARAM)
      {
        // TODO: build this into the Ethos printer??
        // strip off the "(eo::param ...)"
        ret = cur[0];
      }
      else if (childChanged)
      {
        ret = Expr(d_state.mkExprSimple(k, children));
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(t) != visited.end());
  Assert(!visited.find(t)->second.isNull());
  return visited[t];
}

Expr Desugar::mkRequiresModelSat(bool tgt, const Expr& test, const Expr& ret)
{
  std::vector<Expr> modelSatArgs;
  modelSatArgs.push_back(d_peoModelSat);
  modelSatArgs.push_back(test);
  Expr t1 = d_state.mkExpr(Kind::APPLY, modelSatArgs);
  if (StdPlugin::optionVcUseModelStrict())
  {
    Expr t2 = mkOptionSome(tgt);
    return mkRequiresEq(t1, t2, ret);
  }
  else
  {
    Expr t2 = mkOptionSome(!tgt);
    return mkRequiresEq(t1, t2, ret, true);
  }
}

Expr Desugar::mkRequiresModelTypeofBool(const Expr& test, const Expr& ret)
{
  std::vector<Expr> modelTypeofArgs;
  modelTypeofArgs.push_back(d_peoModelTypeof);
  modelTypeofArgs.push_back(test);
  Expr t1 = d_state.mkExpr(Kind::APPLY, modelTypeofArgs);
  return mkRequiresEq(t1, d_boolType, ret);
}

Expr Desugar::mkRequiresModelIsInput(const Expr& test, const Expr& ret)
{
  std::vector<Expr> modelSatArgs;
  modelSatArgs.push_back(d_peoModelIsInput);
  modelSatArgs.push_back(test);
  Expr t1 = d_state.mkExpr(Kind::APPLY, modelSatArgs);
  Expr t2 = d_state.mkTrue();
  return mkRequiresEq(t1, t2, ret);
}

Expr Desugar::mkRequiresEq(const Expr& t1,
                           const Expr& t2,
                           const Expr& ret,
                           bool neg)
{
  std::vector<Expr> children;
  children.push_back(neg ? d_peoRequiresDeq : d_peoRequiresEq);
  children.push_back(t1);
  children.push_back(t2);
  children.push_back(ret);
  return d_state.mkExpr(Kind::APPLY, children);
}

Expr Desugar::mkOptionSome(bool val)
{
  std::vector<Expr> children;
  children.push_back(d_peoOptionSome);
  children.push_back(d_state.mkBool(val));
  return d_state.mkExpr(Kind::APPLY, children);
}

Attr Desugar::getAttribute(const Expr& e)
{
  std::map<Expr, std::pair<Attr, Expr>>::iterator it = d_attrDecl.find(e);
  if (it != d_attrDecl.end())
  {
    return it->second.first;
  }
  return Attr::NONE;
}

}  // namespace ethos
