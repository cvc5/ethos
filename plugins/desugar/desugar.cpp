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
  d_any = d_state.mkSymbol(Kind::PARAM, "Any", d_state.mkType());
  // we require santization of the eo::List at this stage
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

void Desugar::finalizeProgram(const Expr& e, const Expr& prog, std::ostream& os)
{
#if 0
  std::vector<std::pair<Expr, Expr>> evals = FlattenEval::flattenProgram(d_state, e, prog);
  if (!evals.empty())
  {
    for (std::pair<Expr, Expr>& fe : evals)
    {
      finalizeProgramInternal(fe.first, fe.second, os);
    }
  }
#endif
  Expr p = e;
  Expr pt = d_tc.getType(p);
  std::vector<Expr> pandt{pt, prog};
  std::vector<Expr> vars = Expr::getVariables(pandt);
  os << "; " << (prog.isNull() ? "fwd-decl: " : "program: ") << e << std::endl;
  os << "(program " << e << " (";
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
    printTerm(pt[i], os);
  }
  os << ") ";
  printTerm(pt[pargs], os);
  os << std::endl;
  if (!prog.isNull())
  {
    os << "  (" << std::endl;
    for (size_t i = 0, ncases = prog.getNumChildren(); i < ncases; i++)
    {
      const Expr& c = prog[i];
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
    bool isAmb = (cattr == Attr::AMB || cattr == Attr::AMB_DATATYPE_CONSTRUCTOR);
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
          // skip
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
    // if ambiguous, go back and print the remaining parameters
    if (isAmb)
    {
      Assert (argTypes[0].getKind()==Kind::QUOTE_TYPE);
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
    os << ")" << std::endl;
  }
  else
  {
    os << "const " << cname << " ";
    printTerm(ct, os);
    os << ")" << std::endl;
  }
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
      d_eoNilNground << "(program " << pname << " (($eo_T Type) ";
      printParamList(nvars, d_eoNilNground, false);
      d_eoNilNground << ")" << std::endl;
      d_eoNilNground << "  :signature ((eo::quote $eo_T)) $eo_T" << std::endl;
      d_eoNilNground << "  (" << std::endl;
      d_eoNilNground << "  ((" << pname << " ";
      printTerm(ct[0], d_eoNilNground);
      d_eoNilNground << ") ";
      printTerm(cattrCons, d_eoNilNground);
      d_eoNilNground << ")" << std::endl;
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
            sslc << "(eo::requires ($eo_typeof " << arg << ") ";
            printTerm(cta, sslc);
            sslc << " ";
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
      Kind ak = (cattr == Attr::OPAQUE && pattern == e) ? Kind::APPLY_OPAQUE
                                                        : Kind::APPLY;
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

void Desugar::printParamListOld(const std::vector<Expr>& vars,
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
#if 0
  // Make program

#else
  // std::cout << "Finalize " << r << std::endl;
  // std::cout << "Type is " << rto << std::endl;
  //  compile to Eunoia program
  Expr rt = mkSanitize(rto);
  // std::cout << "...santized to " << rt << std::endl;

  d_eoVc << "; rule: " << e << std::endl;
  if (rt.getKind() != Kind::FUNCTION_TYPE)
  {
    // ground rule is just a formula definition
    Assert(rt.getKind() == Kind::PROOF_TYPE);
    Expr rrt = rt[0];
    d_eoVc << "(program $eor_" << e << " (($eo_x Bool))" << std::endl;
    d_eoVc << "  :signature (Bool) Bool" << std::endl;
    d_eoVc << "  (" << std::endl;
    d_eoVc << "  (($eor_" << e << " $eo_x) ";
    printTerm(rrt, d_eoVc);
    d_eoVc << ")" << std::endl;
    d_eoVc << "  )" << std::endl;
    d_eoVc << ")" << std::endl;
    if (!d_state.isProofRuleSorry(e.getValue()))
    {
      d_eoVc << "; verification: " << e << std::endl;
      d_eoVc << "(program $eovc_" << e << " (($eo_x Bool))" << std::endl;
      d_eoVc << "  :signature (Bool) Bool" << std::endl;
      d_eoVc << "  (" << std::endl;
      d_eoVc << "  (($eovc_" << e
             << " $eo_x) (eo::requires ($eo_model_sat ($eor_" << e;
      d_eoVc << " $eo_x)) false true))" << std::endl;
      d_eoVc << "  )" << std::endl;
      d_eoVc << ")" << std::endl;
      d_eoVc << std::endl;
    }
    // write a command to indicate that we should process the above vc
    d_eoVc << "(echo \"smt-meta $eovc_" << e << "\")" << std::endl;
    return;
  }

  std::vector<Expr> vars = Expr::getVariables(rt);
  std::stringstream plout;
  std::vector<Expr> params;
  std::map<Expr, bool> pvisited;
  bool pfirstParam = true;
  // TODO: remove
  printParamListOld(vars, plout, params, false, pvisited, pfirstParam);

  std::stringstream tcrSig;
  std::stringstream tcrBody;
  std::stringstream tcrCall;
  for (size_t i = 0, nparams = params.size(); i < nparams; i++)
  {
    Expr v = params[i];
    if (std::find(vars.begin(), vars.end(), v) == vars.end())
    {
      continue;
    }
    Expr tv = d_tc.getType(v);
    if (i > 0)
    {
      tcrSig << " ";
    }
    printTerm(tv, tcrSig);
    tcrSig << " Type";
    tcrBody << " " << v << " ";
    printTerm(tv, tcrBody);
    tcrCall << " " << v << " ($eo_model_typeof " << v << ")";
  }

  std::map<Expr, Expr> evMap = d_overloadSanVisited;
  size_t eVarCount = 0;
  std::vector<std::pair<Expr, Expr>> newVars;
  std::vector<bool> argIsProof;
  std::vector<Expr> finalArgs;
  Assert(rt.getKind() == Kind::FUNCTION_TYPE);
  std::stringstream typeList;
  std::stringstream argList;
  std::vector<Expr> finalVars;
  for (size_t i = 1, nargs = rt.getNumChildren(); i < nargs; i++)
  {
    if (i > 1)
    {
      typeList << " ";
    }
    Expr argTypeo = rt[i - 1];
    Expr argType = mkSanitize(argTypeo, evMap, eVarCount, true, newVars);
    Kind ak = argType.getKind();
    if (ak == Kind::QUOTE_TYPE || ak == Kind::PROOF_TYPE)
    {
      // handled the same: argument is first child
      Expr aa = argType[0];
      Expr ta = d_tc.getType(aa);
      if (ta.isNull())
      {
        // EO_FATAL() << "Could not get type of " << aa << std::endl;
        ta = d_any;
        finalVars.push_back(ta);
      }
      bool isProof = (ak == Kind::PROOF_TYPE);
      printTerm(ta, typeList);
      argList << " ";
      printTerm(argType[0], argList);
      argIsProof.push_back(isProof);
      finalArgs.push_back(argType[0]);
    }
  }
  // print all final variables
  for (std::pair<Expr, Expr>& p : newVars)
  {
    finalVars.push_back(p.first);
  }
  // TODO: remove
  printParamListOld(finalVars, plout, params, false, pvisited, pfirstParam);
  // strip off the "(Proof ...)", which may be beneath requires
  Expr rrt = rt[rt.getNumChildren() - 1];
  std::vector<Expr> reqs;
  while (rrt.getKind() == Kind::EVAL_REQUIRES)
  {
    reqs.push_back(d_state.mkPair(rrt[0], rrt[1]));
    rrt = rrt[2];
  }
  Assert(rrt.getKind() == Kind::PROOF_TYPE);
  rrt = rrt[0];
  rrt = d_state.mkRequires(reqs, rrt);
  // just use the same parameter list
  d_eoVc << "(program $eorx_" << e << " (" << plout.str() << ")" << std::endl;
  d_eoVc << "  :signature (" << tcrSig.str() << ") Bool" << std::endl;
  d_eoVc << "  (" << std::endl;
  d_eoVc << "  (($eorx_" << e << tcrBody.str() << ") ";
  printTerm(rrt, d_eoVc);
  d_eoVc << ")" << std::endl;
  d_eoVc << "  )" << std::endl;
  d_eoVc << ")" << std::endl;
  d_eoVc << "(program $eor_" << e << " (" << plout.str() << ")" << std::endl;
  d_eoVc << "  :signature (" << typeList.str() << ")";
  d_eoVc << " Bool" << std::endl;
  d_eoVc << "  (" << std::endl;
  d_eoVc << "  (($eor_" << e << argList.str() << ") ($eorx_" << e
         << tcrCall.str() << "))" << std::endl;
  d_eoVc << "  )" << std::endl;
  d_eoVc << ")" << std::endl;
  // compile the verification condition for the soundness of this rule
  if (!d_state.isProofRuleSorry(e.getValue()))
  {
    d_eoVc << "; verification: " << e << std::endl;
    d_eoVc << "(program $eovc_" << e << " (" << plout.str() << ")" << std::endl;
    d_eoVc << "  :signature (" << typeList.str() << ")";
    d_eoVc << " Bool" << std::endl;
    d_eoVc << "  (" << std::endl;
    d_eoVc << "  (($eovc_" << e << argList.str() << ")" << std::endl;
    std::stringstream ssvce;
    for (size_t i = 0, nargs = finalArgs.size(); i < nargs; i++)
    {
      if (argIsProof[i])
      {
        d_eoVc << "     (eo::requires ($eo_model_sat " << finalArgs[i]
               << ") true" << std::endl;
        ssvce << ")";
      }
    }
    d_eoVc << "     (eo::requires ($eo_model_sat ($eor_" << e << argList.str()
           << ")) false" << std::endl;
    d_eoVc << "       true))" << ssvce.str() << std::endl;
    d_eoVc << "  )" << std::endl;
    d_eoVc << ")" << std::endl;
    d_eoVc << std::endl;
  }
  d_eoVc << std::endl;
  // write a command to indicate that we should process the above vc
  d_eoVc << "(echo \"smt-meta $eovc_" << e << "\")" << std::endl;
#endif
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
  // finalize the literal type declaration
  d_litTypeDecl << "(define $eo_Numeral () " << d_ltNum.str() << ")"
                << std::endl;
  d_litTypeDecl << "(define $eo_Rational () " << d_ltRational.str() << ")"
                << std::endl;
  d_litTypeDecl << "(define $eo_String () " << d_ltString.str() << ")"
                << std::endl;
  d_litTypeDecl << "(define $eo_Binary () " << d_ltBinary.str() << ")"
                << std::endl;
  d_litTypeDecl << "; decimal and hexadecimal omitted for now." << std::endl;

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
  std::stringstream wfDefs;
  // generate well-foundedness method
  // size_t pcIdCount = 0;
  // std::map<Expr, size_t> pcId;
  std::stringstream os;
  os << "(declare-const @pcall (-> $eo_Numeral $eo_List Type))" << std::endl;
  os << "(program $eovcwf_rec ((pc $eo_Numeral))" << std::endl;
  os << "  :signature ($eo_Numeral $eo_List $eo_List) Bool" << std::endl;
  os << "  (" << std::endl;
  os << "  )" << std::endl;
  os << ")" << std::endl;
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
      if (inPatMatch && ret.getNumChildren() > 0 && ret.isEvaluatable())
      {
        varCount++;
        std::stringstream ssv;
        ssv << "$ex_" << varCount;
        Expr v = d_state.mkSymbol(Kind::PARAM, ssv.str(), d_any);
        newVars.emplace_back(v, ret);
        ret = v;
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(t) != visited.end());
  Assert(!visited.find(t)->second.isNull());
  return visited[t];
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
