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

bool isEunoiaKind(TermKind tk)
{
  return tk==TermKind::EUNOIA_DT_CONS || tk==TermKind::EUNOIA_TERM || tk==TermKind::EUNOIA_SMT_TERM_CONS;
}

// std::string s_path = "/mnt/nfs/clasnetappvm/grad/ajreynol/ethos/";
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

bool SmtMetaReduce::printEmbAtomicTerm(const Expr& c, std::ostream& os, bool inSmtTerm)
{
  // TODO: take inSmtTerm into account??
  std::string cname;
  TermKind tk = getTermKind(c, cname);
  Kind k = c.getKind();
  if (isProgram(c))
  {
    os << c;
    // std::cout << "program const: " << c << " " << d_eoTmpNil << " " <<
    // (c==d_eoTmpNil) << std::endl;
    return true;
  }
  if (k == Kind::CONST)
  {
    if (tk==TermKind::INTERNAL)
    {
      os << cname;
    }
    else if (isEunoiaKind(tk))
    {
      os << "eo." << cname;
    }
    else
    {
      os << "sm." << cname;
    }
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
    os << "(eo.SmtTerm sm." << (l->d_bool ? "True" : "False") << ")";
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
  // third tuple is whether we are in an SMT term
  std::map<Expr, std::string>::iterator it;
  std::vector<std::tuple<Expr, std::string, bool>> visit;
  std::tuple<Expr, std::string, bool> cur;
  visit.emplace_back(c, initCtx, false);
  do
  {
    cur = visit.back();
    visit.pop_back();
    Expr tcur = std::get<0>(cur);
    std::string currTerm = std::get<1>(cur);
    bool inSmtTerm = std::get<2>(cur);
    Kind ck = tcur.getKind();
    std::stringstream cname;
    bool printArgs = false;
    size_t printArgStart = 0;
    if (ck == Kind::APPLY && !isProgram(tcur[0]))
    {
      // Determine if this is a Eunoia internal term, or an
      // SMT term
      std::string smConsName;
      if (!inSmtTerm && !isEunoiaSymbol(tcur[0], smConsName))
      {
        os << (nconj > 0 ? " " : "") << "((_ is eo.SmtTerm) " << currTerm
           << ")";
        nconj++;
        std::stringstream sssn;
        sssn << "(eo.to_smt " << currTerm << ")";
        currTerm = sssn.str();
        cname << "sm.Apply";
        inSmtTerm = true;
      }
      else
      {
        cname << (inSmtTerm ? "sm" : "eo") << ".Apply";
      }
      printArgs = true;
    }
    else if (ck == Kind::FUNCTION_TYPE)
    {
      // TODO: can this occur?
      // maybe if reasoning about function as first class argument?
      cname << "eo.FunType";
      printArgs = true;
    }
    else if (ck == Kind::APPLY_OPAQUE)
    {
      printEmbAtomicTerm(tcur[0], cname);
      printArgStart = 1;
      printArgs = true;
    }
    if (printArgs)
    {
      // argument must be an apply
      os << (nconj > 0 ? " " : "") << "((_ is " << cname.str() << ") "
         << currTerm << ")";
      nconj++;
      for (size_t i = printArgStart, nchild = tcur.getNumChildren();
           i < nchild;
           i++)
      {
        std::stringstream ssNext;
        ssNext << "(" << cname.str() << ".arg" << (i + 1 - printArgStart) << " "
               << currTerm << ")";
        visit.emplace_back(tcur[i], ssNext.str(), inSmtTerm);
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
      it = ctx.d_ctx.find(tcur);
      if (it == ctx.d_ctx.end())
      {
        // find time seeing this parameter, it is bound to the selector chain
        ctx.d_ctx[tcur] = currTerm;
      }
      else
      {
        os << (nconj > 0 ? " " : "") << "(= " << currTerm << " " << it->second
           << ")";
        nconj++;
      }
    }
    else
    {
      std::stringstream atomTerm;
      if (printEmbAtomicTerm(tcur, atomTerm))
      {
        os << (nconj > 0 ? " " : "") << "(= " << currTerm << " "
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
  /*
  // TODO: this is probably impossible without a sanitize step.
  std::map<const ExprValue*, size_t> lbind;
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
    std::erase(ll.begin(), ll.end()
  }
  std::map<const ExprValue*, size_t>::iterator itl;
  */
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
    std::vector<std::tuple<Expr, size_t, bool>> visit;
    std::tuple<Expr, size_t, bool> cur;
    Expr recTerm;
    visit.emplace_back(t, 0, false);
    do
    {
      cur = visit.back();
      recTerm = std::get<0>(cur);
      size_t childIndex = std::get<1>(cur);
      bool inSmtTerm = std::get<2>(cur);
      itsa = smtAppToTuple.find(recTerm);
      if (itsa != smtAppToTuple.end())
      {
        recTerm = itsa->second;
      }
      // if we are printing the head of the term
      if (childIndex == 0)
      {
        /*
        itl = lbind.find(cur.first.getValue());
        if (itl != lbind.end() && itl->second != i)
        {
          os << "y" << itl->second;
          visit.pop_back();
          continue;
        }
        */
        Kind ck = recTerm.getKind();
        if (ck == Kind::PARAM)
        {
          it = ctx.d_ctx.find(recTerm);
          Assert(it != ctx.d_ctx.end()) << "Cannot find " << recTerm;
          os << it->second;
          visit.pop_back();
          continue;
        }
        else if (recTerm.getNumChildren() == 0)
        {
          if (!printEmbAtomicTerm(recTerm, os))
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
            // std::cout << "Check if apply term " << recTerm << std::endl;
            Assert (smtAppToTuple.find(recTerm)==smtAppToTuple.end());
            if (isEoToSmt(recTerm[0]) || isSmtToEo(recTerm[0]))
            {
              // do not write sm.Apply
            }
            else if (isSmtApplyTerm(recTerm, smtAppName, smtArgs))
            {
              // testers introduced in model_smt layer handled specially
              if (smtAppName.compare(0, 3, "is ") == 0)
              {
                os << "(_ is " << smtAppName.substr(3) << ") ";
              }
              else
              {
                // std::cout << "...returns true!!!! name is \"" << smtAppName
                // <<
                // "\"" << std::endl;
                os << smtAppName << " ";
              }
              // we recurse on the compiled SMT arguments
              recTerm = d_state.mkExprSimple(Kind::TUPLE, smtArgs);
              // std::cout << recTerm << " is " << smtAppName << " / " <<
              // recTerm << std::endl;
              smtAppToTuple[recTerm] = recTerm;
            }
            else if (!inSmtTerm && !isEunoiaTerm(recTerm[0]) && !isProgram(recTerm[0]))
            {
              os << "sm.Apply ";
              // our children are now each SMT terms.
              std::get<1>(visit.back())++;
              std::get<1>(visit.back())++;
              visit.emplace_back(recTerm[1], 0, true);
              visit.emplace_back(recTerm[0], 0, true);
              continue;
            }
            else if (!isProgram(recTerm[0]))
            {
              Assert(recTerm.getNumChildren() == 2);
              // could use macro to ensure "Stuck" propagates
              // NOTE: if we have the invariant that we pattern matched, we don't need to check
              os << "$eo_Apply ";
            }
          }
          else if (ck == Kind::APPLY_OPAQUE)
          {
            // kind is ignored, prints as a multi argument function
          }
          else if (ck == Kind::FUNCTION_TYPE)
          {
            Assert(recTerm.getNumChildren() == 2);
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
            EO_FATAL() << "Unhandled kind " << ck << " " << recTerm
                       << std::endl;
          }
          std::get<1>(visit.back())++;
          visit.emplace_back(recTerm[0], 0, inSmtTerm);
        }
      }
      else if (childIndex >= recTerm.getNumChildren())
      {
        os << ")";
        visit.pop_back();
      }
      else
      {
        // another argument
        Assert(childIndex < recTerm.getNumChildren());
        os << " ";
        std::get<1>(visit.back())++;
        visit.emplace_back(recTerm[childIndex], 0, inSmtTerm);
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
        d_defs << "(" << vname.str() << " eo.Term)";
      }
      d_defs << ") eo.Term ";
      // TODO: check if a Eunoia term here???
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
  std::string pname;
  TermKind tk = getTermKind(v, pname);
  if (pname == "eo.to_smt")
  {
    return;
  }
  // things that are manually axiomatized
  if (tk==TermKind::SMT_PROGRAM || tk==TermKind::EUNOIA_PROGRAM)
  {
    return;
  }
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
    decl << "eo.Term";
    std::stringstream ssArg;
    ssArg << "x" << i;
    appTerm << " " << ssArg.str();
    args.emplace_back(ssArg.str());
    varList << "(" << ssArg.str() << " eo.Term)";
    stuckCond << " (= " << ssArg.str() << " eo.Stuck)";
  }
  if (nargs > 2)
  {
    stuckCond << ")";
  }
  appTerm << ")";
  decl << ") eo.Term)" << std::endl;
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
  cases << "    eo.Stuck" << std::endl;
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
    d_defs << "(define-fun " << v << " (" << varList.str() << ") eo.Term"
           << std::endl;
  }
  d_defs << cases.str();
  d_defs << "    eo.Stuck";
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
    std::string consName;
    TermKind tk = getTermKind(e, consName);
    // ignore deep embeddings of smt terms
    // all symbols beginning with @ are not part of term definition
    if (tk==TermKind::INTERNAL || tk==TermKind::SMT_TERM_TYPE)
    {
      continue;
    }
    bool isEunoia = isEunoiaKind(tk);
    std::stringstream* out = isEunoia ? &d_eoTermDecl : &d_termDecl;
    (*out) << "  ; declare " << consName << std::endl;
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
    cname << (isEunoia ? "eo." : "sm.") << consName;
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
      bool isEunoiaArg = isEunoia;
      // corner case: if this is the SMT term constructor, is it an SMT term
      if (tk == TermKind::EUNOIA_SMT_TERM_CONS)
      {
        isEunoiaArg = false;
      }
      (*out) << ".arg" << (i + 1) << " ";
      // if we are an SMT-LIB literal constructor, we take the opaque types
      if (tk == TermKind::SMT_DT_CONS)
      {
        Assert (ct[i].getKind()==Kind::QUOTE_TYPE);
        Expr targ = ct[i][0];
        Expr ttarg = d_tc.getType(targ);
        (*out) << ttarg;
      }
      else
      {
        (*out) << (isEunoiaArg ? "eo." : "sm.") << "Term";
      }
      (*out) << ")";
    }
    (*out) << ")" << std::endl;
    // is it an SMT-LIB symbol????
    //std::stringstream ss;
    //ss << e;
    //std::string name = ss.str();
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
    // NOTE: this is intentionally quantifying on sm.Term, not eo.Term.
    // In other words, this conjectures that there is an sm.Term, that
    // when embedded into Eunoia witnesses the unsoundness.
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
        call << " (eo.SmtTerm x" << i << ")";
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
  // these terms totally disappear
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
  if (sname == "$smt_Term" || sname == "eo.Stuck")
  {
    return true;
  }
  return false;
}
bool SmtMetaReduce::isEunoiaSymbol(const Expr& t, std::string& name)
{
  TermKind tk = getTermKind(t, name);
  return isEunoiaKind(tk);
}

TermKind SmtMetaReduce::getTermKind(const Expr& e, std::string& name)
{
  if (isInternalSymbol(e))
  {
    return TermKind::INTERNAL;
  }
  std::stringstream ss;
  ss << e;
  std::string sname = ss.str();
  if (sname == "$smt_Term")
  {
    name = sname;
    return TermKind::SMT_TERM_TYPE;
  }
  if (sname.compare(0, 8, "$smd_eo.")==0)
  {
    name = sname.substr(8);
    if (name=="SmtTerm")
    {
      return TermKind::EUNOIA_SMT_TERM_CONS;
    }
    return TermKind::EUNOIA_DT_CONS;
  }
  else if (sname.compare(0, 8, "$smd_sm.")==0)
  {
    name = sname.substr(8);
    return TermKind::SMT_DT_CONS;
  }
  if (sname.compare(0, 1, "@") == 0 || sname.compare(0, 8, "$eo_List") == 0)
  {
    name = sname;
    return TermKind::EUNOIA_TERM;
  }
  if (sname.compare(0,7, "$sm_mk_")==0)
  {
    name = sname;
    return TermKind::SMT_PROGRAM;
  }
  if (sname.compare(0,7,"$eo_mk_")==0)
  {
    name = sname;
    return TermKind::EUNOIA_PROGRAM;
  }
  name = sname;
  return TermKind::SMT_TERM;
}

bool SmtMetaReduce::isEunoiaTerm(const Expr& t)
{
  Expr tcur = t;
  while (tcur.getKind()==Kind::APPLY)
  {
    // TODO: is this right???
    if (isSmtToEo(tcur[0]))
    {
      return false;
    }
    tcur = tcur[0];
  }
  std::string name;
  return isEunoiaSymbol(tcur, name);
}

bool SmtMetaReduce::isProgram(const Expr& t)
{
  if (t.getKind()==Kind::PROGRAM_CONST)
  {
    return true;
  }
  std::string name;
  TermKind tk = getTermKind(t, name);
  return tk==TermKind::SMT_PROGRAM || tk==TermKind::EUNOIA_PROGRAM;
}

}  // namespace ethos
