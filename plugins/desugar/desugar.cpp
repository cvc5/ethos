/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "smt_meta_reduce.h"

#include "state.h"
#include <fstream>
#include <sstream>
#include <string>

namespace ethos {

//std::string s_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
std::string s_path = "/home/andrew/ethos/";

Desugar::Desugar(State& s) : d_state(s), d_tc(s.getTypeChecker()) {
  d_listNil = s.mkListNil();
  d_listCons = s.mkListCons();
  d_listType = s.mkListType();
  d_inInitialize = false;
}

Desugar::~Desugar() {}

void Desugar::initialize()
{
  // initially include bootstrapping definitions
  d_inInitialize = true;
  std::stringstream ss;
  ss << s_path << "plugins/desugar/eo_core.eo";
  d_state.includeFile(ss.str(), true);
  d_eoTmpInt = d_state.getVar("$eo_tmp_Int");
  Assert (!d_eoTmpInt.isNull());
  d_eoTmpNil = d_state.getVar("$eo_tmp_nil");
  Assert (!d_eoTmpNil.isNull());

  //std::cout << "Forward declares: " << d_eoTmpInt << " " << d_eoTmpNil << std::endl;
  d_inInitialize = false;
}

void Desugar::reset() {}

void Desugar::pushScope() {}

void Desugar::popScope() {}

void Desugar::includeFile(const Filepath& s, bool isReference, const Expr& referenceNf) {}

void Desugar::setLiteralTypeRule(Kind k, const Expr& t)
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
    d_numDecl << ss.str();
    d_num << t;
  }
  else
  {
    d_defs << ss.str();
  }
}

void Desugar::bind(const std::string& name, const Expr& e)
{
  Kind k = e.getKind();
  if (k==Kind::CONST || k==Kind::PROOF_RULE || k==Kind::LAMBDA)
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
  d_defs << "(program " << v;
  d_defs << "  :signature (";
  d_defs << ")" << std::endl;

  d_defs << ")" << std::endl;
}

void Desugar::finalizePrograms()
{
  for (const std::pair<Expr, Expr>& p : d_progSeen)
  {
    if (p.second.getKind()==Kind::LAMBDA)
    {
      // prints as a define-fun
      d_defs << "; define " << p.first << std::endl;
      d_defs << "(define-fun " << p.first << " (";
      Expr e = p.second;
      Assert (e[0].getKind()==Kind::TUPLE);
      SelectorCtx ctx;
      for (size_t i=0, nvars=e[0].getNumChildren(); i<nvars; i++)
      {
        Expr v = e[0][i];
        if (i>0)
        {
          d_defs << " ";
        }
        std::stringstream vname;
        vname << v;
        ctx.d_ctx[v] = vname.str();
        d_defs << "(" << vname.str() << " sm.Term)";
      }
      d_defs << ") sm.Term ";
      printEmbTerm(e[1], d_defs, ctx);
      d_defs << ")" << std::endl << std::endl;
      continue;
    }
    finalizeProgram(p.first, p.second);
  }
  d_progSeen.clear();
}

void Desugar::finalizeProgram(const Expr& v, const Expr& prog)
{
  if (v==d_eoTmpNil)
  {
    return;
  }
  d_defs << "; " << (prog.isNull() ? "fwd-decl: " : "program: ") << v << std::endl;
  std::stringstream decl;
  Expr vv = v;
  Expr vt = d_tc.getType(vv);
  decl << "(declare-fun " << v << " (";
  std::stringstream varList;
  Assert (vt.getKind()==Kind::PROGRAM_TYPE);
  size_t nargs = vt.getNumChildren();
  Assert (nargs>1);
  std::vector<std::string> args;
  std::stringstream appTerm;
  appTerm << "(" << v;
  std::stringstream stuckCond;
  if (nargs>2)
  {
    stuckCond << " (or";
  }
  for (size_t i=1; i<nargs; i++)
  {
    if (i>1)
    {
      decl << " ";
      varList << " ";
    }
    decl << "sm.Term";
    std::stringstream ssArg;
    ssArg << "x" << i;
    appTerm << " " << ssArg.str();
    args.emplace_back(ssArg.str());
    varList << "(" << ssArg.str() << " sm.Term)";
    stuckCond << " (= " << ssArg.str() << " sm.Stuck)";
  }
  if (nargs>2)
  {
    stuckCond << ")";
  }
  appTerm << ")";
  decl << ") sm.Term)" << std::endl;
  // if forward declared, we are done for now
  if (prog.isNull())
  {
    d_progDeclProcessed.insert(v);
    d_defs << decl.str() << std::endl;
    return;
  }
  bool reqAxiom = (d_progDeclProcessed.find(v)!=d_progDeclProcessed.end());
  // compile the pattern matching
  std::stringstream cases;
  std::stringstream casesEnd;
  // start with stuck case
  cases << "  (ite" << stuckCond.str() << std::endl;
  cases << "    sm.Stuck" << std::endl;
  casesEnd << ")";
  size_t ncases = prog.getNumChildren();
  for (size_t i=0; i<ncases; i++)
  {
    const Expr& c = prog[i];
    const Expr& hd = c[0];
    const Expr& body = c[1];
    // if recursive, needs axiom
    if (!reqAxiom && hasSubterm(body, v))
    {
      reqAxiom = true;
    }
    SelectorCtx ctx;
    std::stringstream currCase;
    size_t nconj = 0;
    for (size_t j=1, nhdchild=hd.getNumChildren(); j<nhdchild; j++)
    {
      // print the pattern matching predicate for this argument, all concatenated together
      printEmbPatternMatch(hd[j], args[j-1], currCase, ctx, nconj);
    }
    // compile the return for this case
    std::stringstream currRet;
    printEmbTerm(body, currRet, ctx);
    // now print the case/return
    cases << "  (ite ";
    printConjunction(nconj, currCase.str(), cases, ctx);
    cases << std::endl;
    cases << "    " << currRet.str() << std::endl;
    casesEnd << ")";
  }
  // axiom
  if (reqAxiom)
  {
    // declare now if not already forward declared
    if (d_progDeclProcessed.find(v)==d_progDeclProcessed.end())
    {
      d_defs << decl.str();
    }
    d_defs << "(assert (forall (" << varList.str() << ")" << std::endl;
    d_defs << "  (= " << appTerm.str() << std::endl;
    casesEnd << "))";
  }
  else
  {
    d_defs << "(define-fun " << v << " (" << varList.str() << ") sm.Term" << std::endl;
  }
  d_defs << cases.str();
  d_defs << "    sm.Stuck";
  d_defs << casesEnd.str() << std::endl;
  d_defs << ")" << std::endl;
  d_defs << std::endl;

}

void Desugar::finalizeDeclarations() {
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  for (const Expr& e : d_declSeen)
  {
    if (e==d_eoTmpInt || e==d_eoTmpNil)
    {
      continue;
    }
    if (e==d_listType || e==d_listCons || e==d_listNil)
    {
      continue;
    }
    d_termDecl << "  ; declare " << e << std::endl;
    Expr c = e;
    Expr ct = d_tc.getType(c);
    //d_termDecl << "  ; type is " << ct << std::endl;
    Attr attr = Attr::NONE;
    Expr attrCons;
    it = d_attrDecl.find(e);
    if (it!=d_attrDecl.end())
    {
      attr = it->second.first;
      attrCons = it->second.second;
    }
    //d_termDecl << "  ; attr is " << attr << std::endl;
    d_termDecl << "  (";
    std::stringstream cname;
    printEmbAtomicTerm(c, cname);
    d_termDecl << cname.str();
    size_t nopqArgs = 0;
    if (attr==Attr::OPAQUE)
    {
      // opaque symbols are non-nullary constructors
      Assert(ct.getKind() == Kind::FUNCTION_TYPE);
      nopqArgs = ct.getNumChildren() - 1;
    }
    else if (attr==Attr::AMB || attr==Attr::DATATYPE_CONSTRUCTOR)
    {
      nopqArgs = 1;
    }
    for (size_t i=0; i<nopqArgs; i++)
    {
      d_termDecl << " (" << cname.str();
      d_termDecl << ".arg" << (i+1) << " sm.Term)";
    }
    d_termDecl << ")" << std::endl;

    if (attr==Attr::RIGHT_ASSOC_NIL || attr==Attr::LEFT_ASSOC_NIL)
    {
      Assert (ct.getKind()==Kind::FUNCTION_TYPE);
      Assert (!attrCons.isNull());
      SelectorCtx nilCtx;
      std::stringstream ncase;
      std::stringstream nret;
      ncase << "((_ is " << cname.str() << ") x1)";
      size_t nconj = 1;
      // only matters if nil is non-ground
      if (!attrCons.isGround())
      {
        printEmbPatternMatch(ct[0], "x2", ncase, nilCtx, nconj);
      }
      d_eoNil << "  (ite ";
      printConjunction(nconj, ncase.str(), d_eoNil, nilCtx);
      d_eoNil << std::endl;
      d_eoNil << "    ";
      printEmbTerm(attrCons, d_eoNil, nilCtx);
      d_eoNil << std::endl;
      d_eoNilEnd << ")";
    }
    // if its type is ground, the type is taken into account for typeof
    Expr pattern = e;
    std::stringstream typeOfCond;
    size_t nTypeOfCond = 0;
    SelectorCtx typeofCtx;
    if (!ct.isGround())
    {
      Assert(ct.getKind() == Kind::FUNCTION_TYPE);
      //std::cout << "Non-ground function type: " << e << " : " << ct << std::endl;
      //std::cout << "Attribute is " << attr << std::endl;
      // We traverse to a position where the type of a partial application
      // of this operator has ground type.
      std::vector<Expr> argTypes;
      std::vector<Expr> allVars = Expr::getVariables(ct);
      while (ct.getKind()==Kind::FUNCTION_TYPE)
      {
        std::vector<Expr> args;
        args.push_back(pattern);
        size_t nargs = ct.getNumChildren();
        for (size_t i=1; i<nargs; i++)
        {
          Expr cta = ct[i-1];
          Expr arg;
          if (cta.getKind()==Kind::QUOTE_TYPE)
          {
            arg = cta[0];
          }
          else
          {
            arg = d_state.mkSymbol(Kind::PARAM, "tmp", cta);
            arg = d_state.mkExpr(Kind::ANNOT_PARAM, {arg, cta});
          }
          args.push_back(arg);
          argTypes.push_back(cta);
        }
        Kind ak = (nopqArgs>0 && pattern==e) ? Kind::APPLY_OPAQUE : Kind::APPLY;
        pattern = d_state.mkExprSimple(ak, args);
        //std::cout << "...pattern is now " << pattern << " from " << args << std::endl;
        ct = ct[nargs-1];
        // maybe we are now fully bound?
        std::vector<Expr> vars = Expr::getVariables(argTypes);
        if (allVars.size()==vars.size())
        {
          break;
        }
      }
      //std::cout << "Partial app that has ground type: " << pattern << std::endl;
      // we now write the pattern matching for the derived pattern.
    }
    printEmbPatternMatch(pattern, "x1", typeOfCond, typeofCtx, nTypeOfCond);
    d_eoTypeof << "  ; type-rule: " << e << std::endl;
    d_eoTypeof << "  (ite ";
    printConjunction(nTypeOfCond, typeOfCond.str(), d_eoTypeof, typeofCtx);
    d_eoTypeof << std::endl;
    d_eoTypeof << "    ";
    printEmbTerm(ct, d_eoTypeof, typeofCtx);
    d_eoTypeof << std::endl;
    d_eoTypeofEnd << ")";
  }
  d_declSeen.clear();
}

void Desugar::finalizeRules()
{
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  for (const Expr& e : d_ruleSeen)
  {
    // ignore those with :sorry
    if (d_state.isProofRuleSorry(e.getValue()))
    {
      continue;
    }
    finalizeRule(e);
  }
  d_ruleSeen.clear();
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
        // will instantiate it to strip off "(eo::param ...)"
        Expr dummy = d_state.mkSymbol(Kind::PARAM, cname.str(), tcur);
        keep.push_back(dummy);
        ectx[cur.getValue()] = dummy.getValue();
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
        // instantiate it, which strips off "(eo::param ...)"
        Expr atev = d_tc.evaluate(argType[0].getValue(), ectx);
        argList << " " << atev;
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
    d_eoRules << "(program $sm.exec_" << e << " (" << paramList.str() << ")" << std::endl;
    d_eoRules << "  :signature (" << tcrSig.str() << ") Bool" << std::endl;
    d_eoRules << "  (" << std::endl;
    d_eoRules << "  (($sm.exec_" << e << tcrBody.str() << ") " << rrt << ")" << std::endl;
    d_eoRules << "  )" << std::endl;
    d_eoRules << ")" << std::endl;
    d_eoRules << "(program $sm_" << e << " (" << paramList.str() << ")" << std::endl;
    d_eoRules << "  :signature (" << typeList.str() << ")";
    d_eoRules << " Bool" << std::endl;
    d_eoRules << "  (" << std::endl;
    d_eoRules << "  (($sm_" << e << argList.str() << ") ($sm.exec_" << e << tcrCall.str() << "))" << std::endl;
    d_eoRules << "  )" << std::endl;
    d_eoRules << ")" << std::endl;
    d_eoRules << std::endl;
  }
  else
  {
    // ground rule is just a formula definition
    Assert (rt.getKind()==Kind::PROOF_TYPE);
    Expr rrt = rt[0];
    d_eoRules << "(define $sm_" << e << " () " << rrt << ")" << std::endl << std::endl;
  }

}

void Desugar::finalize()
{
  std::set<Expr> declProcessed;
  for (std::pair<Expr, Kind>& d : d_declSeen)
  {
    if (k==Kind::NUMERAL)
    {
      // defines
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
  ssie << s_path << "plugins/desugar/eo_desugar.eo";
  std::ifstream ine(ssie.str());
  std::ostringstream sse;
  sse << ine.rdbuf();
  std::string finalEo = sse.str();
  
  replace(finalEo, "$EO_RULES$", d_eoRules.str());
  
  std::stringstream ssoe;
  ssoe << s_path << "plugins/desugar/eo_desugar_gen.eo";
  std::ofstream oute(ssoe.str());
  oute << finalEo;
}

std::string toString() {
  std::stringstream ss;
  return ss.str();
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
