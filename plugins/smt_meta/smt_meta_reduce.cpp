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
  d_sufToKind["bool"] = Kind::BOOLEAN;
  d_sufToKind["z"] = Kind::NUMERAL;
  d_sufToKind["q"] = Kind::RATIONAL;
  d_sufToKind["str"] = Kind::STRING;
  d_sufToKind["bin"] = Kind::BINARY;
}

SmtMetaReduce::~SmtMetaReduce() {}

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
  // os << ctx.d_letBegin.str();
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
  // os << ctx.d_letEnd.str();
}

bool SmtMetaReduce::printEmbAtomicTerm(const Expr& c, std::ostream& os)
{
  Kind k = c.getKind();
  if (k == Kind::CONST)
  {
    if (isInternalSymbol(c))
    {
      os << c;
    }
    else if (isEunoiaSymbol(c))
    {
      os << "(sm.EoTerm eo." << c << ")";
    }
    else
    {
      os << "sm." << c;
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
    /*
    else if (ck == Kind::ANNOT_PARAM)
    {
      visit.emplace_back(cur.first[0], cur.second);
      // its type must match the second argument
      std::stringstream ssty;
      ssty << "($eo_typeof " << cur.second << ")";
      visit.emplace_back(cur.first[1], ssty.str());
    }
    */
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
                                 const SelectorCtx& ctx)
{
  // os << ctx.d_letBegin.str();
  std::map<Expr, std::string>::const_iterator it;
  std::stringstream osEnd;
  std::vector<Expr> ll;
  // maps smt apply terms to the tuple that they actually are
  std::map<Expr, Expr> smtAppToTuple;
  std::map<Expr, Expr>::iterator itsa;
  // letify parameters for efficiency?
  std::map<const ExprValue*, size_t> lbind;
  /*
  lbind = Expr::computeLetBinding(body, ll);
  std::vector<const ExprValue*> toErase;
  // do not letify terms that are SMT apply terms
  for (std::pair<const ExprValue* const, size_t>& lbs : lbind)
  {
    Expr t(lbs.first);
    if (isSmtApplyTerm(t))
    {
      toErase.push_back(lbs.first);
    }
  }
  for (const ExprValue * e : toErase)
  {
    lbind.erase(e);
    std::
  }
  */
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
    Expr recTerm;
    visit.emplace_back(t, 0);
    do
    {
      cur = visit.back();
      recTerm = cur.first;
      itsa = smtAppToTuple.find(recTerm);
      if (itsa != smtAppToTuple.end())
      {
        recTerm = itsa->second;
      }
      // if we are printing the head of the term
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
        if (ck == Kind::PARAM)
        {
          it = ctx.d_ctx.find(cur.first);
          Assert(it != ctx.d_ctx.end()) << "Cannot find " << cur.first;
          os << it->second;
          visit.pop_back();
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
            // maybe its an SMT-apply
            std::string smtAppName;
            std::vector<Expr> smtArgs;
            // std::cout << "Check if apply term " << cur.first << std::endl;
            if (isEoToSmt(cur.first[0]) || isSmtToEo(cur.first[0]))
            {
              // do not write sm.Apply
            }
            else if (isSmtApplyTerm(cur.first, smtAppName, smtArgs))
            {
              // testers introduced in model_smt layer handled specially
              if (smtAppName.compare(0,3, "is ")==0)
              {
                os << "(_ is " << smtAppName.substr(3) << ") ";
              }
              else
              {
                // std::cout << "...returns true!!!! name is \"" << smtAppName <<
                // "\"" << std::endl;
                os << smtAppName << " ";
              }
              // we recurse on the compiled SMT arguments
              recTerm = d_state.mkExprSimple(Kind::TUPLE, smtArgs);
              // std::cout << cur.first << " is " << smtAppName << " / " <<
              // recTerm << std::endl;
              smtAppToTuple[cur.first] = recTerm;
            }
            else
            {
              if (cur.first[0].getKind() != Kind::PROGRAM_CONST)
              {
                Assert(cur.first.getNumChildren() == 2);
                // must use macro to ensure "Stuck" propagates
                os << "$sm_Apply ";
              }
            }
          }
          else if (ck == Kind::APPLY_OPAQUE)
          {
            // kind is ignored, prints as a multi argument function
          }
          else if (ck == Kind::FUNCTION_TYPE)
          {
            Assert(cur.first.getNumChildren() == 2);
            // must use macro to ensure "Stuck" propagates
            os << "$sm_FunType ";
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
            EO_FATAL() << "Unhandled kind " << ck << " " << cur.first
                       << std::endl;
          }
          visit.back().second++;
          visit.emplace_back(recTerm[0], 0);
        }
      }
      else if (cur.second >= recTerm.getNumChildren())
      {
        os << ")";
        visit.pop_back();
      }
      else
      {
        Assert(cur.second < recTerm.getNumChildren());
        os << " ";
        visit.back().second++;
        visit.emplace_back(recTerm[cur.second], 0);
      }
    } while (!visit.empty());
    if (i < nll)
    {
      os << "))";
    }
  }
  os << osEnd.str();
  // os << ctx.d_letEnd.str();
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
    d_defs << "(assert (! (forall (" << varList.str() << ")" << std::endl;
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
  if (reqAxiom)
  {
    d_defs << " :named sm.axiom." << v << ")";
  }
  d_defs << ")" << std::endl;
  d_defs << std::endl;
}

void SmtMetaReduce::finalizeDeclarations()
{
  std::map<Expr, std::pair<Attr, Expr>>::iterator it;
  for (const Expr& e : d_declSeen)
  {
    // ignore deep embeddings of smt terms
    // all symbols beginning with @ are not part of term definition
    if (isInternalSymbol(e))
    {
      continue;
    }
    bool isEunoia = isEunoiaSymbol(e);
    std::stringstream* out = isEunoia ? &d_eoTermDecl : &d_termDecl;
    (*out) << "  ; declare " << e << std::endl;
    Expr c = e;
    Expr ct = d_tc.getType(c);
    // (*out) << "  ; type is " << ct << std::endl;
    Attr attr = Attr::NONE;
    Expr attrCons;
    it = d_attrDecl.find(e);
    if (it != d_attrDecl.end())
    {
      attr = it->second.first;
      attrCons = it->second.second;
    }
    // (*out) << "  ; attr is " << attr << std::endl;
    (*out) << "  (";
    std::stringstream cname;
    cname << (isEunoia ? "eo." : "sm.") << c;
    (*out) << cname.str();
    size_t nopqArgs = 0;
    if (attr == Attr::OPAQUE)
    {
      // opaque symbols are non-nullary constructors
      Assert(ct.getKind() == Kind::FUNCTION_TYPE);
      nopqArgs = ct.getNumChildren() - 1;
    }
    else if (attr == Attr::AMB || attr == Attr::AMB_DATATYPE_CONSTRUCTOR)
    {
      nopqArgs = 1;
    }
    for (size_t i = 0; i < nopqArgs; i++)
    {
      (*out) << " (" << cname.str();
      (*out) << ".arg" << (i + 1) << " sm.Term)";
    }
    (*out) << ")" << std::endl;
    // is it an SMT-LIB symbol????
    std::stringstream ss;
    ss << e;
    std::string name = ss.str();
  }
  d_declSeen.clear();
}

void SmtMetaReduce::finalize()
{
  finalizePrograms();
  finalizeDeclarations();

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

  replace(finalSm, "$SM_TERM_DECL$", d_termDecl.str());
  replace(finalSm, "$SM_EO_TERM_DECL$", d_eoTermDecl.str());
  replace(finalSm, "$SM_DEFS$", d_defs.str());
  replace(finalSm, "$SMT_VC$", d_smtVc.str());

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

bool SmtMetaReduce::echo(const std::string& msg)
{
  if (msg.compare(0, 9, "smt-meta ") == 0)
  {
    std::string eosc = msg.substr(9);
    Expr vv = d_state.getVar(eosc);
    if (vv.isNull())
    {
      EO_FATAL()
          << "When making verification condition, could not find program "
          << eosc;
    }
    d_smtVc << ";;;; final verification condition for " << eosc << std::endl;
    Expr vt = d_tc.getType(vv);
    std::stringstream varList;
    d_smtVc << "(assert (! ";
    if (vt.getKind() == Kind::PROGRAM_TYPE)
    {
      d_smtVc << "(exists (";
      std::stringstream call;
      size_t nargs = vt.getNumChildren();
      for (size_t i = 1; i < nargs; i++)
      {
        if (i > 1)
        {
          d_smtVc << " ";
        }
        d_smtVc << "(x" << i << " sm.Term)";
        call << " x" << i;
      }
      d_smtVc << ")" << std::endl;
      d_smtVc << "  (= (" << eosc << call.str() << ") sm.True))";
    }
    else
    {
      d_smtVc << "(= " << eosc << " sm.True)";
    }
    d_smtVc << " :named sm.conjecture." << vv << ")";
    d_smtVc << ")" << std::endl;
    // std::cout << "...set target" << std::endl;
    return false;
  }
  return true;
}

bool SmtMetaReduce::isSmtApplyTerm(const Expr& t)
{
  std::string name;
  std::vector<Expr> args;
  return isSmtApplyTerm(t, name, args);
}

bool SmtMetaReduce::isSmtApplyTerm(const Expr& t,
                                   std::string& name,
                                   std::vector<Expr>& args)
{
  Expr cur = t;
  while (cur.getKind() == Kind::APPLY)
  {
    args.push_back(cur[1]);
    cur = cur[0];
  }
  size_t arity = isSmtApply(cur);
  if (arity > 0)
  {
    Assert(!args.empty());
    Expr sname = args.back();
    args.pop_back();
    std::reverse(args.begin(), args.end());
    if (sname.getKind() != Kind::STRING)
    {
      EO_FATAL() << "Expected string for SMT-LIB app name, got " << sname;
    }
    const Literal* l = sname.getValue()->asLiteral();
    name = l->d_str.toString();
    return true;
  }
  args.clear();
  return false;
}

size_t SmtMetaReduce::isSmtApply(const Expr& t)
{
  if (t.getKind() == Kind::CONST)
  {
    std::stringstream ss;
    ss << t;
    std::string sname = ss.str();
    if (sname.compare(0, 11, "$smt_apply_") == 0)
    {
      std::string sarity = sname.substr(11);
      // always add one
      return std::stoi(sarity) + 1;
    }
  }
  return 0;
}

Kind SmtMetaReduce::getKindForSuffix(const std::string& suf) const
{
  std::map<std::string, Kind>::const_iterator it = d_sufToKind.find(suf);
  if (it != d_sufToKind.end())
  {
    return it->second;
  }
  return Kind::NONE;
}

bool SmtMetaReduce::isSmtTermType(const Expr& t)
{
  std::stringstream ss;
  ss << t;
  std::string sname = ss.str();
  return sname == "$smt_Term";
}
bool SmtMetaReduce::isSmtToEo(const Expr& t)
{
  if (t.getKind() == Kind::CONST)
  {
    std::stringstream ss;
    ss << t;
    std::string sname = ss.str();
    if (sname.compare(0, 11, "$smt_to_eo_") == 0)
    {
      Kind k = getKindForSuffix(sname.substr(11));
      return k != Kind::NONE;
    }
  }
  return false;
}
bool SmtMetaReduce::isEoToSmt(const Expr& t)
{
  if (t.getKind() == Kind::CONST)
  {
    std::stringstream ss;
    ss << t;
    std::string sname = ss.str();
    if (sname.compare(0, 13, "$smt_from_eo_") == 0)
    {
      Kind k = getKindForSuffix(sname.substr(13));
      return k != Kind::NONE;
    }
  }
  return false;
}

bool SmtMetaReduce::isInternalSymbol(const Expr& t)
{
  std::stringstream ss;
  ss << t;
  std::string sname = ss.str();
  if (sname.compare(0, 13, "$smt_from_eo_") == 0)
  {
    return true;
  }
  if (sname.compare(0, 11, "$smt_to_eo_") == 0)
  {
    return true;
  }
  if (sname.compare(0, 11, "$smt_apply_") == 0)
  {
    return true;
  }
  if (sname=="$smt_Term")
  {
    return true;
  }
  return false;
}
bool SmtMetaReduce::isEunoiaSymbol(const Expr& t)
{
  std::stringstream ss;
  ss << t;
  std::string sname = ss.str();
  if (sname.compare(0, 1, "@") == 0)
  {
    return true;
  }
  if (sname.compare(0,8, "$eo_List")==0)
  {
    return true;
  }
  if (sname=="$eo_Var")
  {
    return true;
  }
  return false;
}

}  // namespace ethos
