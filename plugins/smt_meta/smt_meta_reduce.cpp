/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "smt_meta_reduce.h"

#include <fstream>
#include <sstream>
#include <string>

#include "state.h"

namespace ethos {

//std::string s_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
std::string s_path = "/home/andrew/ethos/";

SmtMetaReduce::SmtMetaReduce(State& s) : d_state(s), d_tc(s.getTypeChecker())
{
  d_listNil = s.mkListNil();
  d_listCons = s.mkListCons();
  d_listType = s.mkListType();
}

SmtMetaReduce::~SmtMetaReduce() {}

void SmtMetaReduce::setLiteralTypeRule(Kind k, const Expr& t)
{
  d_eoTypeofLit << "  (ite ((_ is sm.";
  switch (k)
  {
    case Kind::NUMERAL: d_eoTypeofLit << "Numeral"; break;
    case Kind::RATIONAL: d_eoTypeofLit << "Rational"; break;
    case Kind::BINARY: d_eoTypeofLit << "Binary"; break;
    case Kind::STRING: d_eoTypeofLit << "String"; break;
    case Kind::DECIMAL: d_eoTypeofLit << "Decimal"; break;
    case Kind::HEXADECIMAL: d_eoTypeofLit << "Hexadecimal"; break;
    default: EO_FATAL() << "Unknown literal type rule" << k << std::endl; break;
  }
  d_eoTypeofLit << ") x1)" << std::endl;
  d_eoTypeofEnd << ")";
  Expr self = d_state.mkSelf();
  SelectorCtx ctx;
  ctx.d_ctx[self] = "x1";
  d_eoTypeofLit << "    ";
  printEmbTerm(t, d_eoTypeofLit, ctx);
  d_eoTypeofLit << std::endl;
}

void SmtMetaReduce::bind(const std::string& name, const Expr& e)
{
  if (name.compare(0, 4, "$eo_") == 0 && e.getKind() == Kind::LAMBDA)
  {
    Expr p = e;
    // dummy type
    Expr pt = d_state.mkBuiltinType(Kind::LAMBDA);
    Expr tmp = d_state.mkSymbol(Kind::CONST, name, pt);
    d_progSeen.emplace_back(tmp, p);
    return;
  }
  Kind k = e.getKind();
  if (k == Kind::CONST)
  {
    d_declSeen.insert(e);
  }
}

void SmtMetaReduce::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  d_attrDecl[v] = std::pair<Attr, Expr>(a, cons);
}

void SmtMetaReduce::printConjunction(size_t n,
                                     const std::string& conj,
                                     std::ostream& os,
                                     const SelectorCtx& ctx)
{
  os << ctx.d_letBegin.str();
  if (n == 0)
  {
    os << "true";
  }
  else if (n > 1)
  {
    os << "(and ";
    os << conj;
    os << ")";
  }
  else
  {
    os << conj;
  }
  os << ctx.d_letEnd.str();
}

bool SmtMetaReduce::printEmbAtomicTerm(const Expr& c, std::ostream& os)
{
  if (c == d_listCons)
  {
    os << "sm.$eo_List_cons";
    return true;
  }
  if (c == d_listNil)
  {
    os << "sm.$eo_List_nil";
    return true;
  }
  if (c == d_listType)
  {
    os << "sm.$eo_List";
    return true;
  }
  Kind k = c.getKind();
  if (k == Kind::CONST)
  {
    std::map<Expr, size_t>::iterator it = d_overloadId.find(c);
    size_t oid;
    if (it == d_overloadId.end())
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
    if (oid > 0)
    {
      os << "." << (oid + 1);
    }
    return true;
  }
  else if (k == Kind::PROGRAM_CONST)
  {
    os << c;
    // std::cout << "program const: " << c << " " << d_eoTmpNil << " " <<
    // (c==d_eoTmpNil) << std::endl;
    return true;
  }
  else if (k == Kind::TYPE)
  {
    os << "sm.Type";
    return true;
  }
  else if (k == Kind::BOOL_TYPE)
  {
    os << "sm.BoolType";
    return true;
  }
  const Literal* l = c.getValue()->asLiteral();
  if (l == nullptr)
  {
    return false;
  }
  if (k == Kind::BOOLEAN)
  {
    os << "sm." << (l->d_bool ? "True" : "False");
    return true;
  }
  else if (k == Kind::NUMERAL)
  {
    os << "(sm.Numeral ";
    const Integer& ci = l->d_int;
    if (ci.sgn() == -1)
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
  else if (k == Kind::RATIONAL)
  {
    os << "(sm.Rational " << c << ")";
    return true;
  }
  else if (k == Kind::DECIMAL)
  {
    os << "(sm.Decimal " << c << ")";
    return true;
  }
  else if (k == Kind::BINARY || k == Kind::HEXADECIMAL)
  {
    const BitVector& bv = l->d_bv;
    const Integer& bvi = bv.getValue();
    os << "(sm.";
    os << (k == Kind::BINARY ? "Binary " : "Hexadecimal ");
    os << bv.getSize() << " " << bvi.toString() << ")";
    return true;
  }
  else if (k == Kind::STRING)
  {
    os << "(sm.String " << c << ")";
    return true;
  }
  return false;
}

bool SmtMetaReduce::printEmbPatternMatch(const Expr& c,
                                         const std::string& initCtx,
                                         std::ostream& os,
                                         SelectorCtx& ctx,
                                         size_t& nconj)
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
    if (ck == Kind::APPLY && cur.first[0].getKind() != Kind::PROGRAM_CONST)
    {
      cname << "sm.Apply";
      printArgs = true;
    }
    else if (ck == Kind::FUNCTION_TYPE)
    {
      cname << "sm.FunType";
      printArgs = true;
    }
    else if (ck == Kind::APPLY_OPAQUE)
    {
      printEmbAtomicTerm(cur.first[0], cname);
      printArgStart = 1;
      printArgs = true;
    }
    if (printArgs)
    {
      // argument must be an apply
      os << (nconj > 0 ? " " : "") << "((_ is " << cname.str() << ") "
         << cur.second << ")";
      nconj++;
      for (size_t i = printArgStart, nchild = cur.first.getNumChildren();
           i < nchild;
           i++)
      {
        std::stringstream ssNext;
        ssNext << "(" << cname.str() << ".arg" << (i + 1 - printArgStart) << " "
               << cur.second << ")";
        visit.emplace_back(cur.first[i], ssNext.str());
      }
    }
    else if (ck == Kind::ANNOT_PARAM)
    {
      visit.emplace_back(cur.first[0], cur.second);
      // its type must match the second argument
      std::stringstream ssty;
      ssty << "($eo_typeof " << cur.second << ")";
      visit.emplace_back(cur.first[1], ssty.str());
    }
    else if (ck == Kind::PARAM)
    {
      it = ctx.d_ctx.find(cur.first);
      if (it == ctx.d_ctx.end())
      {
        // find time seeing this parameter, it is bound to the selector chain
        ctx.d_ctx[cur.first] = cur.second;
      }
      else
      {
        os << (nconj > 0 ? " " : "") << "(= " << cur.second << " " << it->second
           << ")";
        nconj++;
      }
    }
    else
    {
      std::stringstream atomTerm;
      if (printEmbAtomicTerm(cur.first, atomTerm))
      {
        os << (nconj > 0 ? " " : "") << "(= " << cur.second << " "
           << atomTerm.str() << ")";
        nconj++;
      }
      else
      {
        EO_FATAL() << "Cannot pattern match evaluatable term";
      }
    }
  } while (!visit.empty());
  return true;
}

bool SmtMetaReduce::printEmbTerm(const Expr& body,
                                 std::ostream& os,
                                 const SelectorCtx& ctx,
                                 bool ignorePf)
{
  os << ctx.d_letBegin.str();
  std::map<Expr, std::string>::const_iterator it;
  std::stringstream osEnd;
  std::vector<Expr> ll;
  // letify parameters for efficiency?
  std::map<const ExprValue*, size_t> lbind = Expr::computeLetBinding(body, ll);
  // NOTE: could print the context in the let list?
  std::map<const ExprValue*, size_t>::iterator itl;
  for (size_t i = 0, nll = ll.size(); i <= nll; i++)
  {
    if (i > 0)
    {
      os << " ";
    }
    if (i < nll)
    {
      os << "(let ((y" << i << " ";
      osEnd << ")";
    }
    Expr t = i < nll ? ll[i] : body;
    std::map<Expr, size_t>::iterator itv;
    std::vector<std::pair<Expr, size_t>> visit;
    std::pair<Expr, size_t> cur;
    visit.emplace_back(t, 0);
    do
    {
      cur = visit.back();
      if (cur.second == 0)
      {
        itl = lbind.find(cur.first.getValue());
        if (itl != lbind.end() && itl->second != i)
        {
          os << "y" << itl->second;
          visit.pop_back();
          continue;
        }
        Kind ck = cur.first.getKind();
        if (ck == Kind::PROOF_TYPE && ignorePf)
        {
          visit.pop_back();
          visit.emplace_back(cur.first[0], 0);
          continue;
        }
        if (ck == Kind::PARAM)
        {
          it = ctx.d_ctx.find(cur.first);
          Assert(it != ctx.d_ctx.end()) << "Cannot find " << cur.first;
          os << it->second;
          visit.pop_back();
          continue;
        }
        if (ck == Kind::ANNOT_PARAM)
        {
          // ignored
          visit.pop_back();
          visit.emplace_back(cur.first[0], 0);
          continue;
        }
        if (ck == Kind::PARAMETERIZED)
        {
          Assert(cur.first.getNumChildren() == 2);
          // ignored
          visit.pop_back();
          visit.emplace_back(cur.first[1], 0);
          continue;
        }
        if (ck == Kind::VARIABLE)
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
          if (ck == Kind::APPLY)
          {
            if (cur.first[0].getKind() != Kind::PROGRAM_CONST)
            {
              Assert(cur.first.getNumChildren() == 2);
              os << "sm.Apply ";
            }
          }
          else if (ck == Kind::APPLY_OPAQUE)
          {
            // kind is ignored, prints as a multi argument function
          }
          else if (ck == Kind::FUNCTION_TYPE)
          {
            Assert(cur.first.getNumChildren() == 2);
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
            EO_FATAL() << "Unhandled kind " << ck << " " <<  cur.first << std::endl;
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
        Assert(cur.second < cur.first.getNumChildren());
        os << " ";
        visit.back().second++;
        visit.emplace_back(cur.first[cur.second], 0);
      }
    } while (!visit.empty());
    if (i < nll)
    {
      os << "))";
    }
  }
  os << osEnd.str();
  os << ctx.d_letEnd.str();
  return true;
}

void SmtMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  d_progSeen.emplace_back(v, prog);
}

void SmtMetaReduce::finalizePrograms()
{
  for (const std::pair<Expr, Expr>& p : d_progSeen)
  {
    if (p.second.getKind() == Kind::LAMBDA)
    {
      // prints as a define-fun
      d_defs << "; define " << p.first << std::endl;
      d_defs << "(define-fun " << p.first << " (";
      Expr e = p.second;
      Assert(e[0].getKind() == Kind::TUPLE);
      SelectorCtx ctx;
      for (size_t i = 0, nvars = e[0].getNumChildren(); i < nvars; i++)
      {
        Expr v = e[0][i];
        if (i > 0)
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

void SmtMetaReduce::finalizeProgram(const Expr& v, const Expr& prog)
{
  d_defs << "; " << (prog.isNull() ? "fwd-decl: " : "program: ") << v
         << std::endl;
  std::stringstream decl;
  Expr vv = v;
  Expr vt = d_tc.getType(vv);
  decl << "(declare-fun " << v << " (";
  std::stringstream varList;
  Assert(vt.getKind() == Kind::PROGRAM_TYPE);
  size_t nargs = vt.getNumChildren();
  Assert(nargs > 1);
  std::vector<std::string> args;
  std::stringstream appTerm;
  appTerm << "(" << v;
  std::stringstream stuckCond;
  if (nargs > 2)
  {
    stuckCond << " (or";
  }
  for (size_t i = 1; i < nargs; i++)
  {
    if (i > 1)
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
  if (nargs > 2)
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
  bool reqAxiom = (d_progDeclProcessed.find(v) != d_progDeclProcessed.end());
  // compile the pattern matching
  std::stringstream cases;
  std::stringstream casesEnd;
  // start with stuck case
  cases << "  (ite" << stuckCond.str() << std::endl;
  cases << "    sm.Stuck" << std::endl;
  casesEnd << ")";
  size_t ncases = prog.getNumChildren();
  for (size_t i = 0; i < ncases; i++)
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
    for (size_t j = 1, nhdchild = hd.getNumChildren(); j < nhdchild; j++)
    {
      // print the pattern matching predicate for this argument, all
      // concatenated together
      printEmbPatternMatch(hd[j], args[j - 1], currCase, ctx, nconj);
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
    if (d_progDeclProcessed.find(v) == d_progDeclProcessed.end())
    {
      d_defs << decl.str();
    }
    d_defs << "(assert (forall (" << varList.str() << ")" << std::endl;
    d_defs << "  (= " << appTerm.str() << std::endl;
    casesEnd << "))";
  }
  else
  {
    d_defs << "(define-fun " << v << " (" << varList.str() << ") sm.Term"
           << std::endl;
  }
  d_defs << cases.str();
  d_defs << "    sm.Stuck";
  d_defs << casesEnd.str() << std::endl;
  d_defs << ")" << std::endl;
  d_defs << std::endl;
}

void SmtMetaReduce::finalizeDeclarations()
{
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  for (const Expr& e : d_declSeen)
  {
    if (e == d_listType || e == d_listCons || e == d_listNil)
    {
      continue;
    }
    d_termDecl << "  ; declare " << e << std::endl;
    Expr c = e;
    Expr ct = d_tc.getType(c);
    // d_termDecl << "  ; type is " << ct << std::endl;
    Attr attr = Attr::NONE;
    Expr attrCons;
    it = d_attrDecl.find(e);
    if (it != d_attrDecl.end())
    {
      attr = it->second.first;
      attrCons = it->second.second;
    }
    // d_termDecl << "  ; attr is " << attr << std::endl;
    d_termDecl << "  (";
    std::stringstream cname;
    printEmbAtomicTerm(c, cname);
    d_termDecl << cname.str();
    size_t nopqArgs = 0;
    if (attr == Attr::OPAQUE)
    {
      // opaque symbols are non-nullary constructors
      Assert(ct.getKind() == Kind::FUNCTION_TYPE);
      nopqArgs = ct.getNumChildren() - 1;
    }
    else if (attr == Attr::AMB || attr == Attr::DATATYPE_CONSTRUCTOR)
    {
      nopqArgs = 1;
    }
    for (size_t i = 0; i < nopqArgs; i++)
    {
      d_termDecl << " (" << cname.str();
      d_termDecl << ".arg" << (i + 1) << " sm.Term)";
    }
    d_termDecl << ")" << std::endl;
  }
  d_declSeen.clear();
}

void SmtMetaReduce::finalize()
{
  finalizePrograms();
  finalizeDeclarations();
  // debugging
  /*
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
  */

  auto replace = [](std::string& txt,
                    const std::string& tag,
                    const std::string& replacement) {
    auto pos = txt.find(tag);
    if (pos != std::string::npos)
    {
      txt.replace(pos, tag.length(), replacement);
    }
  };

  // make the final SMT-LIB encoding
  std::stringstream ssi;
  ssi << s_path << "plugins/smt_meta/smt_meta.smt2";
  std::ifstream in(ssi.str());
  std::ostringstream ss;
  ss << in.rdbuf();
  std::string finalSm = ss.str();

  replace(finalSm, "$TERM_DECL$", d_termDecl.str());
  replace(finalSm, "$TYPEOF_LITERALS$", d_eoTypeofLit.str());
  replace(finalSm, "$TYPEOF_END$", d_eoTypeofEnd.str());
  replace(finalSm, "$DEFS$", d_defs.str());
  // replace(finalSm, "$RULES$", d_rules.str());

  // std::cout << ";;; Final: " << std::endl;
  // std::cout << finalSm << std::endl;

  std::stringstream sso;
  sso << s_path << "plugins/smt_meta/smt_meta_gen.smt2";
  std::cout << "Write smt2-defs " << sso.str() << std::endl;
  std::ofstream out(sso.str());
  out << finalSm;
}

bool SmtMetaReduce::hasSubterm(const Expr& t, const Expr& s)
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

}  // namespace ethos
