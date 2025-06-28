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

#include "state.h"

namespace ethos {

//std::string s_ds_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
std::string s_ds_path = "/home/andrew/ethos/";

Desugar::Desugar(State& s) : d_state(s), d_tc(s.getTypeChecker())
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

  // TODO: make this instantiation eo::self??
  d_eoBinaryWidth << "$eo_fail";
}

Desugar::~Desugar() {}

void Desugar::setLiteralTypeRule(Kind k, const Expr& t)
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
    // get the symbols and declare them in the preamble
    std::vector<Expr> syms = getSubtermsKind(Kind::CONST, t);
    for (const Expr& s : syms)
    {
      finalizeDeclaration(s, d_litTypeDecl);
    }
    d_litTypeDecl << "; type-rules: " << k << std::endl;
    d_litTypeDecl << ss.str();
    // it is only possible to define e.g. $eo_Binary
    // if t is ground. This avoids having eo::self as a free parameter.
    // We use $eo_undef_type otherwise.
    if (t.isGround())
    {
      (*os) << t;
    }
    else
    {
      // since $eo_Numeral is used to define the type rules for builtin
      // operators, it must have a simple type.
      // Note that we could introduce a $eo_Builtin_Numeral but this would
      // complicate further type checking, i.e. the user expects
      // the result of eo::len to be an Int.
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

void Desugar::finalizeProgram(const Expr& e, const Expr& prog)
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
          printParamList(vars, os, params, true, visited, firstParam);
        }
        else if ((cattr == Attr::AMB || cattr == Attr::AMB_DATATYPE_CONSTRUCTOR)
                 && i == 0)
        {
          // print the parameters; these will lead to a definition that is
          // ambiguous again.
          std::vector<Expr> avars = Expr::getVariables(v);
          printParamList(vars, os, params, true, visited, firstParam);
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
        printParamList(vars, os, params, true, visited, firstParam);
      }
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
      std::vector<Expr> params;
      printParamList(nvars, d_eoNilNground, params, false);
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
    std::stringstream ssngpat;
    std::stringstream ngSig;
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
            if (!ngscope.empty())
            {
              ngSig << " ";
            }
            ngSig << "$eo_T";
            ssngpat << " " << cta[1];
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
        ssngpat << " ";
        printTerm(cta, ssngpat);
        if (!ngscope.empty())
        {
          ngSig << " ";
        }
        ngSig << "$eo_T";
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
      d_eoTypeofNGround << "(program " << pname << " (($eo_T Type) ";
      std::vector<Expr> ngvs = Expr::getVariables(ngscope);
      std::vector<Expr> ngps;
      printParamList(ngvs, d_eoTypeofNGround, ngps, false);
      d_eoTypeofNGround << ")" << std::endl;
      d_eoTypeofNGround << "  :signature (" << ngSig.str() << ") Type"
                        << std::endl;
      d_eoTypeofNGround << "  (" << std::endl;
      d_eoTypeofNGround << "  ((" << pname << ssngpat.str() << ") ";
      printTerm(ct, d_eoTypeofNGround);
      d_eoTypeofNGround << ")" << std::endl;
      d_eoTypeofNGround << "  )" << std::endl;
      d_eoTypeofNGround << ")" << std::endl;
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
                             std::vector<Expr>& params,
                             bool useImplicit)
{
  std::map<Expr, bool> visited;
  bool firstParam = true;
  printParamList(vars, os, params, useImplicit, visited, firstParam);
}

void Desugar::printParamList(const std::vector<Expr>& vars,
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
  std::vector<Expr> params;
  printParamList(vars, d_defs, params, true);
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
    d_eoVc << "  (($eor_" << e << " $eo_x) " << rrt << ")" << std::endl;
    d_eoVc << "  )" << std::endl;
    d_eoVc << ")" << std::endl;
    if (!d_state.isProofRuleSorry(e.getValue()))
    {
      d_eoVc << "; verification: " << e << std::endl;
      d_eoVc << "(program $eovc_" << e << " (($eo_x Bool))" << std::endl;
      d_eoVc << "  :signature (Bool) Bool" << std::endl;
      d_eoVc << "  (" << std::endl;
      d_eoVc << "  (($eovc_" << e << " $eo_x) (eo::requires ($eo_model_sat ($eor_" << e;
      d_eoVc << " $eo_x)) false true))" << std::endl;
      d_eoVc << "  )" << std::endl;
      d_eoVc << ")" << std::endl;
      d_eoVc << std::endl;
    }
    return;
  }

  std::vector<Expr> vars = Expr::getVariables(rt);
  std::stringstream plout;
  std::vector<Expr> params;
  std::map<Expr, bool> pvisited;
  bool pfirstParam = true;
  printParamList(vars, plout, params, false, pvisited, pfirstParam);

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
    tcrCall << " " << v << " (eo::typeof " << v << ")";
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
  printParamList(finalVars, plout, params, false, pvisited, pfirstParam);
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
  d_eoVc << "  (($eorx_" << e << tcrBody.str() << ") " << rrt << ")"
         << std::endl;
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

  replace(finalEo, "$EO_LITERAL_TYPE_DECL$", d_litTypeDecl.str());
  replace(finalEo, "$EO_NUMERAL$", d_ltNum.str());
  replace(finalEo, "$EO_RATIONAL$", d_ltRational.str());
  replace(finalEo, "$EO_STRING$", d_ltString.str());
  replace(finalEo, "$EO_BINARY$", d_ltBinary.str());
  replace(finalEo, "$EO_DEFS$", d_defs.str());
  replace(finalEo, "$EO_NIL_CASES$", d_eoNil.str());
  replace(finalEo, "$EO_NIL_NGROUND_DEFS$", d_eoNilNground.str());
  replace(finalEo, "$EO_TYPEOF_CASES$", d_eoTypeof.str());
  replace(finalEo, "$EO_TYPEOF_NGROUND_DEFS$", d_eoTypeofNGround.str());
  replace(finalEo, "$EO_DT_CONSTRUCTORS_PARAM$", d_eoDtConsParam.str());
  replace(finalEo, "$EO_DT_CONSTRUCTORS_CASES$", d_eoDtCons.str());
  replace(finalEo, "$EO_DT_SELECTORS_CASES$", d_eoDtSel.str());
  // for model semantics

  replace(finalEo, "$EO_MODEL_CONST_PRED_CASES$", d_eoModelConstPred.str());
  replace(finalEo, "$EO_MODEL_EVAL_CASES$", d_eoModelEval.str());
  replace(finalEo, "$EO_BINARY_WIDTH$", d_eoBinaryWidth.str());
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
  ssoe << s_ds_path << "plugins/desugar/eo_desugar_gen.eo";
  std::cout << "Write core-defs    " << ssoe.str() << std::endl;
  std::ofstream oute(ssoe.str());
  oute << finalEo;
}

void Desugar::finalizeWellFounded()
{
  // TODO
  std::stringstream wfDefs;
  // generate well-foundedness method
  size_t pcIdCount = 0;
  std::map<Expr, size_t> pcId;
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
        // strip off the "(eo::param ...)"
        ret = cur[0];
      }
      else if (k == Kind::VARIABLE)
      {
        Expr tt = d_tc.getType(cur);
        const Literal* l = cur.getValue()->asLiteral();
        Assert(l != nullptr);
        std::vector<Expr> vargs;
        vargs.push_back(d_state.mkLiteral(Kind::STRING, l->toString()));
        vargs.push_back(tt);
        ret = d_state.mkExprSimple(Kind::EVAL_VAR, vargs);
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

std::vector<Expr> Desugar::getSubtermsKind(Kind k, const Expr& t)
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
