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

Desugar::Desugar(State& s) : StdPlugin(s), d_dproof(s, this)
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
  d_overloadSanVisited[d_listType] =
      d_state.mkSymbol(Kind::CONST, "$eo_List", s.mkType());
  Expr pft = s.mkProofType();
  d_overloadSanVisited[pft] =
      d_state.mkSymbol(Kind::CONST, "$eo_Proof", s.mkType());
  d_genVcs = d_state.getOptions().d_pluginDesugarGenVc;
  if (d_genVcs)
  {
    d_eoVc << ";; verification conditions" << std::endl << std::endl;
  }
  d_eoDtConsParamCount = 0;

  d_true = d_state.mkTrue();
  // a placeholder
  d_boolType = d_state.mkBoolType();
  Expr ttype = d_state.mkType();
  Expr modelSatType = d_state.mkProgramType({d_boolType}, d_boolType);
  d_peoModelSat =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_model_sat", modelSatType);
  d_peoModelUnsat =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_model_unsat", modelSatType);
  Expr modelTypeofType = d_state.mkProgramType({d_boolType}, ttype);
  d_peoModelTypeof =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_typeof", modelTypeofType);
  Expr modelIsInputType = d_state.mkProgramType({d_boolType}, d_boolType);
  Expr anyT = allocateTypeVariable();
  Expr anyT2 = allocateTypeVariable();
  Expr eoRequireEqType = d_state.mkProgramType({anyT, anyT, anyT2}, anyT2);
  d_peoRequiresEq =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_requires_eq", eoRequireEqType);
  d_peoRequiresDeq = d_state.mkSymbol(
      Kind::PROGRAM_CONST, "$eo_requires_deq", eoRequireEqType);
  Expr eoProvenType =
      d_state.mkProgramType({d_state.mkProofType()}, d_state.mkBoolType());
  d_peoProven =
      d_state.mkSymbol(Kind::PROGRAM_CONST, "$eo_proven", eoProvenType);
  Expr eoPfType =
      d_state.mkFunctionType({d_state.mkBoolType()}, d_state.mkProofType());
  d_peoPf = d_state.mkSymbol(Kind::CONST, "$eo_pf", eoPfType);
}

Desugar::~Desugar() {}

void Desugar::define(const std::string& name, const Expr& e)
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
}

void Desugar::bind(const std::string& name, const Expr& e)
{
  Kind k = e.getKind();
  if (k == Kind::CONST || k == Kind::PROOF_RULE)
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
  // If it is ambiguous, it won't be ambiguous anymore after desugaring, hence
  // we sanitize it to prevent printing "as" when printing terms here.
  if (isAmb)
  {
    Expr cnamb = d_state.mkSymbol(Kind::CONST, cnss.str(), c.getType());
    d_overloadSanVisited[c] = cnamb;
  }
  Expr cto = d_tc.getType(c);
  Expr ct = cto;
  Trace("desugar") << "Finalize declaration " << e << " " << ct << std::endl;
  std::vector<Expr> argTypes;
  Expr retType;
  std::map<Expr, bool> visited;
  std::vector<Expr> params;
  std::stringstream opaqueArgs;
  if (ct.getKind() == Kind::FUNCTION_TYPE)
  {
    if (cattr == Attr::OPAQUE)
    {
      AppInfo* ainfo = d_state.getAppInfo(e.getValue());
      Expr anum = ainfo->d_attrConsTerm;
      Assert(anum.getKind() == Kind::NUMERAL);
      Assert(anum.getValue()->asLiteral()->d_int.fitsUnsignedInt());
      size_t novars = anum.getValue()->asLiteral()->d_int.toUnsignedInt();
      for (size_t i = 0; i < novars; i++)
      {
        Expr v;
        if (ct[i].getKind()==Kind::QUOTE_TYPE)
        {
          v = ct[i][0];
          Assert(v.getKind() == Kind::PARAM)
              << "Bad opaque function variable " << ct << " for " << c;
        }
        else
        {
          // It may be an ordinary argument in which case we reintroduce the
          // parameter corresponding to the opaque argument.
          std::stringstream ssv;
          ssv << "$eo_ov_" << i;
          v = d_state.mkSymbol(Kind::PARAM, ssv.str(), ct[i]);
        }
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
        if (v.getKind() == Kind::PARAM)
        {
          std::vector<Expr> varsp;
          varsp.push_back(v);
          bool isOpaque = (isAmb && i == 0);
          printParamList(varsp, os, params, visited, true, isOpaque);
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
    os << ") ";
    printTerm(retType, os);
  }
  else
  {
    os << "const " << cname << " ";
    printTerm(ct, os);
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
        ssx << "$eo_x" << argCount;
        Expr arg;
        if (cta.getKind() == Kind::QUOTE_TYPE)
        {
          cta = cta[0];
          // always check type as well
          ngscope.push_back(cta.getType());
          ssngarg << " ($eo_typeof " << ssx.str() << ")";
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
        argTypes.push_back(ngscope[i].getType());
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
  // if marked sorry, we should never do verification
  if (d_state.isProofRuleSorry(e.getValue()))
  {
    return;
  }
  Trace("desugar") << "Finalize rule " << e << std::endl;
  AppInfo* ainfo = d_state.getAppInfo(e.getValue());
  Expr tupleVal = ainfo->d_attrConsTerm;
  Assert(tupleVal.getNumChildren() == 4);
  Expr rprog = tupleVal[3];
  if (!d_genVcs)
  {
    // for nullary proof rules, ensure the definition is preserved
    if (rprog.getKind() != Kind::PROGRAM_CONST)
    {
      d_eoVc << "(define $eo_prog_" << e << " () ";
      printTerm(rprog, d_eoVc);
      d_eoVc << ")" << std::endl;
    }
    // $eo_eq $eo_ite $eo_requires needed for pattern linearization
    d_eoVc << "(echo \"eo-desugar $eo_prog_" << e << " :deps eo-desugar-deps"
           << " \")" << std::endl;
    return;
  }

  Expr progCase;
  if (rprog.getKind() == Kind::PROGRAM_CONST)
  {
    Expr rprogDef = d_state.getProgram(rprog.getValue());
    progCase = rprogDef[0][0];
  }
  else
  {
    progCase = rprog;
  }
  Expr conclusion = progCase;
  std::stringstream pvcname;
  pvcname << "$eovc_" << e;
  Expr unsound = d_true;
  // require that the conclusion is not satisfied
  unsound = mkRequiresModelSat(false, conclusion, unsound);
  if (StdPlugin::optionVcUseTypeof())
  {
    unsound = mkRequiresModelTypeofBool(conclusion, unsound);
  }
  // require that each premise is satisfied
  for (size_t i = 0, nargs = progCase.getNumChildren(); i < nargs; i++)
  {
    size_t ii = nargs - (i + 1);
    if (progCase[ii].getKind() == Kind::PROOF)
    {
      unsound = mkRequiresModelSat(true, progCase[ii][0], unsound);
      if (StdPlugin::optionVcUseTypeof())
      {
        unsound = mkRequiresModelTypeofBool(progCase[ii][0], unsound);
      }
    }
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
  }
  Expr progType = d_state.mkProgramType(uargTypes, d_boolType);
  Expr prog = d_state.mkSymbol(Kind::PROGRAM_CONST, pvcname.str(), progType);
  std::vector<Expr> vcpChildren;
  vcpChildren.push_back(prog);
  vcpChildren.insert(vcpChildren.end(), uvars.begin(), uvars.end());
  Expr progPat = d_state.mkExpr(Kind::APPLY, vcpChildren);
  Expr progPair = d_state.mkPair(progPat, unsound);
  Expr progDef = d_state.mkExpr(Kind::PROGRAM, {progPair});
  finalizeProgram(prog, progDef, d_eoVc);
  // write a command to indicate that we should process the above vc.
  // eo-desugar-vc and eo-desugar-vc-deps are expected to be replaced by the
  // specific use case
  d_eoVc << "(echo \"eo-desugar-vc $eovc_" << e << " :deps eo-desugar-vc-deps"
         << " \")" << std::endl;
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
  // ensure all literal types are defined
  std::set<Kind> literalKinds = {
      Kind::NUMERAL, Kind::RATIONAL, Kind::BINARY, Kind::STRING};
  Expr builtinType;
  for (Kind k : literalKinds)
  {
    if (d_ltKindProcessed.find(k) != d_ltKindProcessed.end())
    {
      continue;
    }
    if (builtinType.isNull())
    {
      builtinType =
          d_state.mkSymbol(Kind::CONST, "$eo_Builtin_Type", d_state.mkType());
    }
    setLiteralTypeRule(k, builtinType);
  }

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

  /*
  std::stringstream ssies;
  ssies << s_plugin_path << "plugins/model_smt/eo_builtin_smt.eo";
  std::ifstream ines(ssies.str());
  std::ostringstream sses;
  sses << ines.rdbuf();
  */

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
  // Verification conditions for *all* proof rules are ready now
  // TODO: make this manual?
  replace(finalEo, "$EO_VC$", d_eoVc.str());
  std::stringstream ssoe;
  ssoe << s_plugin_path << "plugins/desugar/eo_desugar_gen.eo";
  std::cout << "Write core-defs    " << ssoe.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << finalEo;
  oute << std::endl;
  // output steps if applicable
  d_dproof.output(oute);
}

void Desugar::notifyAssume(const std::string& name, Expr& proven, bool isPush)
{
  d_dproof.notifyAssume(name, proven, isPush);
}

bool Desugar::notifyStep(const std::string& name,
                         std::vector<Expr>& children,
                         Expr& rule,
                         Expr& proven,
                         std::vector<Expr>& premises,
                         std::vector<Expr>& args,
                         bool isPop)
{
  return d_dproof.notifyStep(
      name, children, rule, proven, premises, args, isPop);
}

bool Desugar::echo(const std::string& msg) { return true; }

Expr Desugar::mkSanitize(const Expr& t)
{
  // take overloads into account
  std::map<Expr, Expr> visited = d_overloadSanVisited;
  return mkSanitize(t, visited);
}

Expr Desugar::mkSanitize(const Expr& t, std::map<Expr, Expr>& visited)
{
  Assert(!t.isNull());
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
      visited[cur] = d_null;
      for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
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
      for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
      {
        Expr cn = cur[i];
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (k == Kind::PROOF)
      {
        // "pf" is a kind, we handle it specially here by turning it into an
        // ordinary application.
        ret = d_state.mkExprSimple(Kind::APPLY, {d_peoPf, children[0]});
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
  modelSatArgs.push_back(tgt ? d_peoModelSat : d_peoModelUnsat);
  modelSatArgs.push_back(test);
  Expr t1 = d_state.mkExpr(Kind::APPLY, modelSatArgs);
  if (StdPlugin::optionVcUseModelStrict())
  {
    return mkRequiresEq(t1, d_state.mkBool(true), ret);
  }
  else
  {
    // FIXME
    // return mkRequiresEq(t1, t2, ret, true);
    return d_null;
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

Expr Desugar::mkRequiresEq(const Expr& t1,
                           const Expr& t2,
                           const Expr& ret,
                           bool neg)
{
  std::vector<Expr> children;
  children.push_back(t1);
  children.push_back(t2);
  children.push_back(ret);
  return d_state.mkExprSimple(Kind::EVAL_REQUIRES, children);
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

void Desugar::setLiteralTypeRule(Kind k, const Expr& t)
{
  Assert(d_ltKindProcessed.find(k) == d_ltKindProcessed.end());
  d_ltKindProcessed.insert(k);
  // NOTE: literal definitions cannot use any builtin operators
  // that are desugared in the initial step, e.g. eo::list_*.
  // They can use core eo operators that are desugared later
  // e.g. eo::len.
  std::stringstream eoss;
  switch (k)
  {
    case Kind::NUMERAL: eoss << "Numeral"; break;
    case Kind::RATIONAL: eoss << "Rational"; break;
    case Kind::BINARY: eoss << "Binary"; break;
    case Kind::STRING: eoss << "String"; break;
    case Kind::DECIMAL:
    case Kind::HEXADECIMAL: break;
    default: EO_FATAL() << "Unknown literal type rule" << k << std::endl; break;
  }
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
    d_litTypeDecl << "(declare-consts " << literalKindToString(k) << " " << t
                  << ")" << std::endl;
    // A literal type may be non-ground if it uses eo::self.
    // For consistency, we always define the program $eo_lit_type_X, even
    // if the type is ground. We additionally always define the nullary type
    // $eo_X, even if the type is non-ground, in which case we arbitrarily
    // instantiate it with getGroundTermForLiteralKind.
    Expr ltinst = t;
    Expr ltg = t;
    if (t.isGround())
    {
      d_litTypeDecl << "; type-rules: " << k << std::endl;
    }
    else
    {
      Expr ty = d_state.mkSymbol(Kind::CONST, "t", d_state.mkAny());
      Expr gt = getGroundTermForLiteralKind(k);
      ltg = d_tc.getOrSetLiteralTypeRule(k, gt.getValue());
      ltinst = d_tc.getOrSetLiteralTypeRule(k, ty.getValue());
      d_litTypeDecl << "; (approx) type-rules: " << k << std::endl;
    }
    d_litTypeDecl << "(define $eo_" << eoss.str() << " () " << ltg << ")"
                  << std::endl;
    d_litTypeProg << "(program $eo_lit_type_" << eoss.str()
                  << " ((T Type) (t T))" << std::endl;
    d_litTypeProg << "  :signature (T) Type" << std::endl;
    d_litTypeProg << "  (" << std::endl;
    d_litTypeProg << "  (($eo_lit_type_" << eoss.str() << " t) " << ltinst
                  << ")" << std::endl;
    d_litTypeProg << "  )" << std::endl;
    d_litTypeProg << ")" << std::endl;
    // since $eo_Numeral is used to define the type rules for builtin
    // operators, it must have a ground type.
    if (k == Kind::NUMERAL)
    {
      Assert(t.isGround()) << "Must have a ground type for <numeral>.";
    }
  }
}

}  // namespace ethos
