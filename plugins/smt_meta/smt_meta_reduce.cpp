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

SmtMetaReduce::SmtMetaReduce(State& s) : d_state(s), d_tc(s.getTypeChecker()) {
  d_listNil = s.mkListNil();
  d_listCons = s.mkListCons();
  d_listType = s.mkListType();
  d_inInitialize = false;
}

SmtMetaReduce::~SmtMetaReduce() {}

void SmtMetaReduce::initialize()
{
  // initially include bootstrapping definitions
  d_inInitialize = true;
  d_state.includeFile("/home/andrew/ethos/plugins/smt_meta/eo_core.eo", true);
  d_eoTmpInt = d_state.getVar("eo_tmp_Int");
  Assert (!d_eoTmpInt.isNull());
  d_eoTmpNil = d_state.getVar("eo_tmp_nil");
  Assert (!d_eoTmpNil.isNull());
  //std::cout << "Forward declares: " << d_eoTmpInt << " " << d_eoTmpNil << std::endl;
  d_inInitialize = false;
}

void SmtMetaReduce::reset() {}

void SmtMetaReduce::pushScope() {}

void SmtMetaReduce::popScope() {}

void SmtMetaReduce::includeFile(const Filepath& s, bool isReference, const Expr& referenceNf) {}

void SmtMetaReduce::setLiteralTypeRule(Kind k, const Expr& t)
{
  // TODO
  d_eoTypeofLit << "  (ite ((_ is sm.";
  switch (k)
  {
    case Kind::NUMERAL: d_eoTypeofLit << "Numeral"; break;
    case Kind::RATIONAL: d_eoTypeofLit << "Rational"; break;
    case Kind::BINARY: d_eoTypeofLit << "Binary"; break;
    case Kind::STRING: d_eoTypeofLit << "String"; break;
    case Kind::DECIMAL: d_eoTypeofLit << "Decimal"; break;
    case Kind::HEXADECIMAL: d_eoTypeofLit << "Hexadecimal"; break;
    default:
      EO_FATAL() << "Unknown literal type rule" << k << std::endl;
      break;
  }
  d_eoTypeofLit << ") x1)" << std::endl;
  d_eoTypeofEnd << ")";
  Expr self = d_state.mkSelf();
  std::map<Expr, std::string> ctx;
  ctx[self] = "x1";
  d_eoTypeofLit << "    (= ($eo_typeof x1) ";
  printEmbTerm(t, d_eoTypeofLit, ctx);
  d_eoTypeofLit << ")" << std::endl;
}

void SmtMetaReduce::bind(const std::string& name, const Expr& e) {
  if (d_inInitialize)
  {
    if (name.compare(0, 4, "$eo_") == 0 && e.getKind()==Kind::LAMBDA)
    {
      Expr p = e;
      // dummy type
      Expr pt = d_state.mkBuiltinType(Kind::LAMBDA);
      Expr tmp = d_state.mkSymbol(Kind::CONST, name, pt);
      d_progSeen.emplace_back(tmp, p);
      return;
    }
  }
  Kind k = e.getKind();
  if (k==Kind::CONST)
  {
    d_declSeen.insert(e);
  }
  if (k==Kind::PROOF_RULE)
  {
    d_ruleSeen.insert(e);
  }
}

void SmtMetaReduce::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  d_attrDecl[v] = std::pair<Attr, Expr>(a, cons);
}

void SmtMetaReduce::markOracleCmd(const Expr& v, const std::string& ocmd) {}

void SmtMetaReduce::printConjunction(size_t n, const std::string& conj, std::ostream& os)
{
  if (n==0)
  {
    os << "true";
  }
  else if (n>1)
  {
    os << "(and ";
    os << conj;
    os << ")";
  }
  else
  {
    os << conj;
  }
}

bool SmtMetaReduce::printEmbAtomicTerm(const Expr& c, std::ostream& os)
{
  if (c==d_eoTmpInt)
  {
    // FIXME (hack)
    os << "Int";
    return true;
  }
  if (c==d_eoTmpNil)
  {
    os << "$eo_nil";
    return true;
  }
  if (c==d_listCons)
  {
    os << "sm.List.cons";
    return true;
  }
  if (c==d_listNil)
  {
    os << "sm.List.nil";
    return true;
  }
  if (c==d_listType)
  {
    os << "sm.ListType";
    return true;
  }
  Kind k = c.getKind();
  if (k==Kind::CONST)
  {
    std::map<Expr, size_t>::iterator it = d_overloadId.find(c);
    size_t oid;
    if (it==d_overloadId.end())
    {
      std::stringstream ss;
      ss << c;
      std::string s = ss.str();
      oid = d_overloadCount[s];
      d_overloadId[c] = oid;
      d_overloadCount[s]++;
    }
    else
    {
      oid = it->second;
    }
    os << "sm." << c;
    if (oid>0)
    {
      os << "." << (oid+1);
    }
    return true;
  }
  else if (k==Kind::PROGRAM_CONST)
  {
    os << c;
    //std::cout << "program const: " << c << " " << d_eoTmpNil << " " << (c==d_eoTmpNil) << std::endl;
    return true;
  }
  else if (k==Kind::TYPE)
  {
    os << "sm.Type";
    return true;
  }
  else if (k==Kind::BOOL_TYPE)
  {
    os << "sm.BoolType";
    return true;
  }
  const Literal* l = c.getValue()->asLiteral();
  if (l==nullptr)
  {
    return false;
  }
  if (k==Kind::BOOLEAN)
  {
    os << "sm." << (l->d_bool ? "True" : "False");
    return true;
  }
  else if (k==Kind::NUMERAL)
  {
    os << "(sm.Numeral ";
    const Integer& ci = l->d_int;
    if (ci.sgn()==-1)
    {
      const Integer& cin = -ci;
      os << "(- " << cin.toString() << ")";
    }
    else
    {
      os << ci.toString();
    }
    os << ")";
    return true;
  }
  else if (k==Kind::RATIONAL)
  {
    os << "(sm.Rational " << c << ")";
    return true;
  }
  else if (k==Kind::DECIMAL)
  {
    os << "(sm.Decimal " << c << ")";
    return true;
  }
  else if (k==Kind::BINARY || k==Kind::HEXADECIMAL)
  {
    const BitVector& bv = l->d_bv;
    const Integer& bvi = bv.getValue();
    os << "(sm.";
    os << (k==Kind::BINARY ? "Binary " : "Hexadecimal ");
    os  << bv.getSize() << " " << bvi.toString() << ")";
    return true;
  }
  else if (k==Kind::STRING)
  {
    os << "(sm.String " << c << ")";
    return true;
  }
  return false;
}

bool SmtMetaReduce::printEmbPatternMatch(const Expr& c, const std::string& initCtx, std::ostream& os, std::map<Expr, std::string>& ctx, size_t& nconj)
{
  std::map<Expr, std::string>::iterator it;
  std::vector<std::pair<Expr, std::string>> visit;
  std::pair<Expr, std::string> cur;
  visit.emplace_back(c, initCtx);
  do
  {
    cur = visit.back();
    visit.pop_back();
    Kind ck = cur.first.getKind();
    std::stringstream cname;
    bool printArgs = false;
    size_t printArgStart = 0;
    if (ck==Kind::APPLY && cur.first[0].getKind()!=Kind::PROGRAM_CONST)
    {
      cname << "sm.Apply";
      printArgs = true;
    }
    else if (ck==Kind::FUNCTION_TYPE)
    {
      cname << "sm.FunType";
      printArgs = true;
    }
    else if (ck==Kind::APPLY_OPAQUE)
    {
      printEmbAtomicTerm(cur.first[0], cname);
      printArgStart = 1;
      printArgs = true;
    }
    else if (ck==Kind::VARIABLE)
    {
      cname << "sm.Var";
      printArgs = true;
      // TODO: string and type
      EO_FATAL() << "Unhandled variable in pattern";
    }
    if (printArgs)
    {
      // argument must be an apply
      os << (nconj>0 ? " " : "") << "((_ is " << cname.str() << ") " << cur.second << ")";
      nconj++;
      for (size_t i=printArgStart, nchild = cur.first.getNumChildren(); i<nchild; i++)
      {
        std::stringstream ssNext;
        ssNext << "(" << cname.str() << ".arg" << (i+1-printArgStart) << " " << cur.second << ")";
        visit.emplace_back(cur.first[i], ssNext.str());
      }
    }
    else if (ck==Kind::ANNOT_PARAM)
    {
      visit.emplace_back(cur.first[0], cur.second);
      // its type must match the second argument
      std::stringstream ssty;
      ssty << "($eo_typeof " << cur.second << ")";
      visit.emplace_back(cur.first[1], cur.second);
    }
    else if (ck==Kind::PARAM)
    {
      it = ctx.find(cur.first);
      if (it==ctx.end())
      {
        // find time seeing this parameter, it is bound to the selector chain
        ctx[cur.first] = cur.second;
      }
      else
      {
        os << (nconj>0 ? " " : "") << "(= " << cur.second << " " << it->second << ")";
        nconj++;
      }
    }
    else
    {
      std::stringstream atomTerm;
      if (printEmbAtomicTerm(cur.first, atomTerm))
      {
        os << (nconj>0 ? " " : "") << "(= " << cur.second << " " << atomTerm.str() << ")";
        nconj++;
      }
      else
      {
        // TODO: is this correct???
        // This handles cases where it is expected that matching at this point
        // evaluates e.g. based on other arguments. This is used heavily in
        // RARE rules where an argument causes a premise term to evaluate e.g.
        // via eo::list_concat.
        os << "(= " << cur.second;
        printEmbTerm(cur.first, os, ctx);
        os << ")";
      }
    }
  }
  while (!visit.empty());
  return true;
}

bool SmtMetaReduce::printEmbTerm(const Expr& body, std::ostream& os, const std::map<Expr, std::string>& ctx, bool ignorePf)
{
  std::map<Expr, std::string>::const_iterator it;
  std::stringstream osEnd;
  std::vector<Expr> ll;
  std::map<const ExprValue*, size_t> lbind = Expr::computeLetBinding(body, ll);
  // TODO: print the context in the let list?
  std::map<const ExprValue*, size_t>::iterator itl;
  for (size_t i=0, nll=ll.size(); i<=nll; i++)
  {
    if (i>0)
    {
      os << " ";
    }
    if (i<nll)
    {
      os << "(let ((y" << i << " ";
      osEnd << ")";
    }
    Expr t = i<nll ? ll[i] : body;
    std::map<Expr, size_t>::iterator itv;
    std::vector<std::pair<Expr, size_t>> visit;
    std::pair<Expr, size_t> cur;
    visit.emplace_back(t, 0);
    do
    {
      cur = visit.back();
      if (cur.second==0)
      {
        itl = lbind.find(cur.first.getValue());
        if (itl!=lbind.end() && itl->second!=i)
        {
          os << "y" << itl->second;
          visit.pop_back();
          continue;
        }
        Kind ck = cur.first.getKind();
        if (ck==Kind::PROOF_TYPE && ignorePf)
        {
          visit.pop_back();
          visit.emplace_back(cur.first[0], 0);
          continue;
        }
        if (ck==Kind::PARAM)
        {
          it = ctx.find(cur.first);
          Assert (it!=ctx.end()) << "Cannot find " << cur.first;
          os << it->second;
          visit.pop_back();
          continue;
        }
        if (ck==Kind::ANNOT_PARAM)
        {
          // ignored
          visit.pop_back();
          visit.emplace_back(cur.first[0], 0);
          continue;
        }
        if (ck==Kind::PARAMETERIZED)
        {
          Assert (cur.first.getNumChildren()==2);
          // ignored
          visit.pop_back();
          visit.emplace_back(cur.first[1], 0);
          continue;
        }
        if (ck==Kind::VARIABLE)
        {
          visit.back().second++;
          os << "(sm.Var \"";
          os << cur.first;
          os << "\" ";
          Expr vt = d_tc.getType(cur.first);
          visit.emplace_back(vt, 0);
          continue;
        }
        else if (cur.first.getNumChildren() == 0)
        {
          if (!printEmbAtomicTerm(cur.first, os))
          {
            EO_FATAL() << "Unknown atomic term in return " << ck << std::endl;
          }
          visit.pop_back();
          continue;
        }
        else
        {
          os << "(";
          if (ck==Kind::APPLY)
          {
            if (cur.first[0].getKind()!=Kind::PROGRAM_CONST)
            {
              Assert (cur.first.getNumChildren()==2);
              os << "sm.Apply ";
            }
          }
          else if (ck==Kind::FUNCTION_TYPE)
          {
            Assert (cur.first.getNumChildren()==2);
            os << "sm.FunType ";
          }
          else if (isLiteralOp(ck))
          {
            std::string kstr = kindToTerm(ck);
            if (kstr.compare(0, 4, "eo::") == 0)
            {
              os << "$eo_" << kstr.substr(4) << " ";
            }
            else
            {
              EO_FATAL() << "Bad name for literal kind " << ck << std::endl;
            }
          }
          else
          {
          }
          visit.back().second++;
          visit.emplace_back(cur.first[0], 0);
        }
      }
      else if (cur.second >= cur.first.getNumChildren())
      {
        os << ")";
        visit.pop_back();
      }
      else
      {
        Assert (cur.second<cur.first.getNumChildren());
        os << " ";
        visit.back().second++;
        visit.emplace_back(cur.first[cur.second], 0);
      }
    }
    while (!visit.empty());
    if (i<nll)
    {
      os << "))";
    }
  }
  os << osEnd.str();
  return true;
}

void SmtMetaReduce::defineProgram(const Expr& v, const Expr& prog) {
  d_progSeen.emplace_back(v, prog);
}

void SmtMetaReduce::finalizePrograms()
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
      std::map<Expr, std::string> ctx;
      for (size_t i=0, nvars=e[0].getNumChildren(); i<nvars; i++)
      {
        Expr v = e[0][i];
        if (i>0)
        {
          d_defs << " ";
        }
        std::stringstream vname;
        vname << v;
        ctx[v] = vname.str();
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

void SmtMetaReduce::finalizeProgram(const Expr& v, const Expr& prog)
{
  std::stringstream decl;
  decl << "; program " << v << std::endl;
  Expr vv = v;
  Expr vt = d_tc.getType(vv);
  decl << "(declare-const " << v << " (-> ";
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
    decl << "sm.Term ";
    if (i>1)
    {
      varList << " ";
    }
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
  decl << "sm.Term)";
  decl << ")" << std::endl;
  if (d_progDeclProcessed.find(v)==d_progDeclProcessed.end())
  {
    d_progDeclProcessed.insert(v);
    d_defs << decl.str();
  }
  // if forward declared, we are done for now
  if (prog.isNull())
  {
    return;
  }
  // compile the pattern matching
  std::stringstream cases;
  std::stringstream casesEnd;
  // start with stuck case
  cases << "  (ite" << stuckCond.str() << std::endl;
  cases << "    (= " << appTerm.str() << " sm.Stuck)" << std::endl;
  casesEnd << ")";
  size_t ncases = prog.getNumChildren();
  for (size_t i=0; i<ncases; i++)
  {
    const Expr& c = prog[i];
    const Expr& hd = c[0];
    const Expr& body = c[1];
    std::map<Expr, std::string> paramToSelector;
    std::map<Expr, std::string>::iterator it;
    std::stringstream currCase;
    size_t nconj = 0;
    for (size_t j=1, nhdchild=hd.getNumChildren(); j<nhdchild; j++)
    {
      // print the pattern matching predicate for this argument, all concatenated together
      printEmbPatternMatch(hd[j], args[j-1], currCase, paramToSelector, nconj);
    }
    // compile the return for this case
    std::stringstream currRet;
    printEmbTerm(body, currRet, paramToSelector);
    // now print the case/return
    cases << "  (ite ";
    printConjunction(nconj, currCase.str(), cases);
    cases << std::endl;
    cases << "    (= " << appTerm.str() << " " << currRet.str() << ")" << std::endl;
    casesEnd << ")";
  }
  // axiom
  d_defs << "(assert (forall (" << varList.str() << ")" << std::endl;
  d_defs << cases.str();
  d_defs << "    (= " << appTerm.str() << " sm.Stuck)";
  d_defs << casesEnd.str() << std::endl;
  d_defs << "))" << std::endl;
  d_defs << std::endl;

}

void SmtMetaReduce::finalizeDeclarations() {
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
    std::map<Expr, std::string> typeofCtx;
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

    if (attr==Attr::RIGHT_ASSOC_NIL)
    {
      Assert (ct.getKind()==Kind::FUNCTION_TYPE);
      Assert (!attrCons.isNull());
      std::map<Expr, std::string> nilCtx;
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
      printConjunction(nconj, ncase.str(), d_eoNil);
      d_eoNil << std::endl;
      d_eoNil << "    (= ($eo_nil x1 x2) ";
      printEmbTerm(attrCons, d_eoNil, nilCtx);
      d_eoNil << ")" << std::endl;
      d_eoNilEnd << ")";
    }
    // if its type is
    if (ct.isGround())
    {
      d_eoTypeof << "  (ite ((_ is " << cname.str() << ") x1)" << std::endl;
      d_eoTypeof << "    (= ($eo_typeof x1) ";
      printEmbTerm(ct, d_eoTypeof, typeofCtx);
      d_eoTypeof << ")" << std::endl;
      d_eoTypeofEnd << ")";
    }
  }
  d_declSeen.clear();
}

void SmtMetaReduce::finalizeRules()
{
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  for (const Expr& e : d_ruleSeen)
  {
    // ignore those with :sorry
    if (d_state.isProofRuleSorry(e.getValue()))
    {
      continue;
    }
    d_rules << "; rule: " << e << std::endl;
    Attr attr = Attr::NONE;
    Expr attrCons;
    it = d_attrDecl.find(e);
    if (it!=d_attrDecl.end())
    {
      attr = it->second.first;
      attrCons = it->second.second;
    }
    //d_rules << "; attribute is " << attr << std::endl;
    Expr r = e;
    Expr rt = d_tc.getType(r);
    //d_rules << "; type is " << rt << std::endl;
    std::stringstream typeVarList;
    std::stringstream argList;
    std::stringstream appTerm;
    std::stringstream proofPred;
    size_t nproofPredConj = 0;
    std::map<Expr, std::string> ctx;
    std::stringstream rcase;
    size_t nconj = 0;
    //d_rules << "(declare-const " << r;
    Expr retType;
    if (rt.getKind()==Kind::FUNCTION_TYPE)
    {
      appTerm << "(" << r;
      //d_rules << " (->";
      // uses flat function type
      for (size_t i=1, nargs = rt.getNumChildren(); i<nargs; i++)
      {
        //d_rules << " sm.Term";
        std::stringstream ssArg;
        ssArg << "x" << i;
        if (i>1)
        {
          typeVarList << " ";
        }
        typeVarList << "(" << ssArg.str() << " sm.Term)";
        Expr argType = rt[i-1];
        Kind ak = argType.getKind();
        Expr toMatch;
        if (ak==Kind::QUOTE_TYPE)
        {
          toMatch = argType[0];
        }
        else if (ak==Kind::PROOF_TYPE)
        {
          toMatch = argType[0];
          if (nproofPredConj>0)
          {
            proofPred << " ";
          }
          nproofPredConj++;
          if (attr==Attr::PREMISE_LIST)
          {
            proofPred << "(sm.hasProofList ";
            Assert (!attrCons.isNull());
            printEmbAtomicTerm(attrCons, proofPred);
            proofPred  << " " << ssArg.str() << ")";
          }
          else
          {
            proofPred << "(sm.hasProof " << ssArg.str() << ")";
          }
        }
        else
        {
          EO_FATAL() << "Unknown type to rule " << ak << std::endl;
        }
        // print the pattern matching
        printEmbPatternMatch(toMatch, ssArg.str(), rcase, ctx, nconj);
      }
      appTerm << ")";
      //d_rules << " sm.Term)";
      retType = rt[rt.getNumChildren()-1];
    }
    else
    {
      appTerm << r;
      //d_rules << " sm.Term";
      retType = rt;
    }
    //d_rules << ")" << std::endl;
    // print the conclusion term
    std::stringstream rret;
    printEmbTerm(retType, rret, ctx, true);

    std::stringstream ruleEnd;
    d_rules << "(assert";
    if (!typeVarList.str().empty())
    {
      d_rules << " (forall (" << typeVarList.str() << ")" << std::endl;
      ruleEnd << ")";
    }
    d_rules << "  (let ((conc " << rret.str() << "))" << std::endl;
    // premises
    if (nproofPredConj>0)
    {
      d_rules << "  (=> ";
      printConjunction(nproofPredConj, proofPred.str(), d_rules);
      d_rules << std::endl;
      ruleEnd << ")";
    }
    // pattern matching
    if (nconj>0)
    {
      d_rules << "  (=> ";
      printConjunction(nconj, rcase.str(), d_rules);
      d_rules << std::endl;
      ruleEnd << ")";
    }
    // type check the conclusion to Bool
    d_rules << "  (=> (= ($eo_typeof conc) sm.BoolType)" << std::endl;
    d_rules << "  (sm.hasProof conc))" << std::endl;
    d_rules << ruleEnd.str() << "))" << std::endl;
    d_rules << std::endl;
  }
  d_ruleSeen.clear();
}

void SmtMetaReduce::finalize() {
  finalizePrograms();
  finalizeDeclarations();
  finalizeRules();
  // debugging
  std::cout << ";;; Term declaration" << std::endl;
  std::cout << d_termDecl.str();
  std::cout << ";;; definitions" << std::endl;
  std::cout << d_defs.str();
  std::cout << ";;; $eo_nil definition" << std::endl;
  std::cout << "var list: " << d_eoNilVarList.str() << std::endl;
  std::cout << d_eoNil.str();
  std::cout << ";;; $eo_typeof literal definition" << std::endl;
  std::cout << d_eoTypeofLit.str();
  std::cout << ";;; $eo_typeof definition" << std::endl;
  std::cout << d_eoTypeof.str();
  std::cout << ";;; proof rules" << std::endl;
  std::cout << d_rules.str();

  std::ifstream in("/home/andrew/ethos/plugins/smt_meta/smt_meta.smt2");
  std::ostringstream ss;
  ss << in.rdbuf();
  std::string finalSm = ss.str();

  auto replace = [](std::string& txt,
                  const std::string& tag,
                  const std::string& replacement) {
    auto pos = txt.find(tag);
    if (pos != std::string::npos)
    {
      txt.replace(pos, tag.length(), replacement);
    }
  };
  replace(finalSm, "$TERM_DECL$", d_termDecl.str());
  replace(finalSm, "$TYPEOF_LITERALS$", d_eoTypeofLit.str());
  replace(finalSm, "$TYPEOF$", d_eoTypeof.str());
  replace(finalSm, "$TYPEOF_END$", d_eoTypeofEnd.str());
  replace(finalSm, "$NIL$", d_eoNil.str());
  replace(finalSm, "$NIL_END$", d_eoNilEnd.str());
  replace(finalSm, "$DEFS$", d_defs.str());
  replace(finalSm, "$RULES$", d_rules.str());
  replace(finalSm, "$HAS_PROOF_LIST$", d_hasProofList.str());

  std::cout << ";;; Final: " << std::endl;
  std::cout << finalSm << std::endl;

  std::ofstream out("/home/andrew/ethos/plugins/smt_meta/smt_meta_gen.smt2");
  out << finalSm;
}

std::string toString() {
  std::stringstream ss;
  return ss.str();
}

}  // namespace ethos
