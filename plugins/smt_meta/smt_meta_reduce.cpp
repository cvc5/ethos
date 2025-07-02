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

// #define NEW_DEF

class ConjPrint
{
 public:
  ConjPrint() : d_npush(0) {}
  void push(const std::string& str)
  {
    if (d_npush > 0)
    {
      d_ss << " ";
    }
    d_ss << str;
    d_npush++;
  }
  std::stringstream d_ss;
  size_t d_npush;
};

SelectorCtx::SelectorCtx() {}
void SelectorCtx::clear()
{
  d_ctx.clear();
  d_tctx.clear();
  d_typeMatch.clear();
}

SmtMetaReduce::SmtMetaReduce(State& s) : StdPlugin(s) {}

SmtMetaReduce::~SmtMetaReduce() {}

bool isEunoiaKind(TermKind tk)
{
  return tk == TermKind::EUNOIA_DT_CONS || tk == TermKind::EUNOIA_TERM;
}
std::string termContextKindToString(TermContextKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case TermContextKind::EUNOIA: ss << "EUNOIA"; break;
    case TermContextKind::SMT: ss << "SMT"; break;
    case TermContextKind::SMT_BUILTIN: ss << "SMT_BUILTIN"; break;
    case TermContextKind::SMT_TYPE: ss << "SMT_TYPE"; break;
    case TermContextKind::SMT_VALUE: ss << "SMT_VALUE"; break;
    case TermContextKind::PROGRAM: ss << "PROGRAM"; break;
    default: ss << "?TermContextKind"; break;
  }
  return ss.str();
}
std::string termContextKindToPrefix(TermContextKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case TermContextKind::EUNOIA: ss << "eo."; break;
    case TermContextKind::SMT: ss << "sm."; break;
    case TermContextKind::SMT_TYPE: ss << "tsm."; break;
    case TermContextKind::SMT_VALUE: ss << "vsm."; break;
    default: ss << "?TermContextKindPrefix"; break;
  }
  return ss.str();
}
std::string termContextKindToCons(TermContextKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case TermContextKind::SMT: ss << "SmtTerm"; break;
    case TermContextKind::SMT_TYPE: ss << "SmtType"; break;
    case TermContextKind::SMT_VALUE: ss << "SmtValue"; break;
    default: ss << "?TermContextKindCons"; break;
  }
  return ss.str();
}

// TODO: clean traces and kinds
std::string termKindToString(TermKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case TermKind::FINAL_EUNOIA_TERM: ss << "FINAL_EUNOIA_TERM"; break;
    case TermKind::FINAL_SMT_TERM: ss << "FINAL_SMT_TERM"; break;
    case TermKind::FINAL_SMT_TYPE: ss << "FINAL_SMT_TYPE"; break;
    case TermKind::FINAL_SMT_VALUE: ss << "FINAL_SMT_VALUE"; break;
    case TermKind::FINAL_VALUE_MAP: ss << "FINAL_VALUE_MAP"; break;
    case TermKind::FINAL_VALUE_STERM_LIST:
      ss << "FINAL_VALUE_STERM_LIST";
      break;
    case TermKind::FINAL_VALUE_RAT_PAIR: ss << "FINAL_VALUE_RAT_PAIR"; break;
    case TermKind::FINAL_BUILTIN_APPLY: ss << "FINAL_BUILTIN_APPLY"; break;
    case TermKind::FINAL_BUILTIN_TYPE: ss << "FINAL_BUILTIN_TYPE"; break;

    // An apply term
    case TermKind::PROGRAM: ss << "PROGRAM"; break;
    // Builtin datatype introduced in model_smt step, for eo.Term
    case TermKind::EUNOIA_DT_CONS: ss << "EUNOIA_DT_CONS"; break;
    // An internal-only symbol defined by the user
    case TermKind::EUNOIA_TERM: ss << "EUNOIA_TERM"; break;
    case TermKind::EUNOIA_BOOL: ss << "EUNOIA_BOOL"; break;
    case TermKind::EUNOIA_TYPE_TYPE: ss << "EUNOIA_TYPE_TYPE"; break;
    case TermKind::EUNOIA_QUOTE_TYPE: ss << "EUNOIA_QUOTE_TYPE"; break;
    // SMT apply
    case TermKind::SMT_BUILTIN_APPLY: ss << "SMT_BUILTIN_APPLY"; break;
    // Builtin datatype introduced in model_smt step, for sm.Term
    case TermKind::SMT_DT_CONS: ss << "SMT_DT_CONS"; break;
    // An SMT term defined by the user (possibly non-SMT-LIB standard)
    case TermKind::SMT_TERM: ss << "SMT_TERM"; break;
    // The type of SMT lib terms
    case TermKind::SMT_TERM_TYPE: ss << "SMT_TERM_TYPE"; break;
    case TermKind::SMT_TYPE_TYPE: ss << "SMT_TYPE_TYPE"; break;
    case TermKind::SMT_TYPE_DT_CONS: ss << "SMT_TYPE_DT_CONS"; break;
    case TermKind::SMT_STD_TYPE: ss << "SMT_STD_TYPE"; break;
    case TermKind::SMT_BUILTIN_TYPE: ss << "SMT_BUILTIN_TYPE"; break;
    case TermKind::EUNOIA_TERM_TYPE: ss << "EUNOIA_TERM_TYPE"; break;
    // An operator that operates on native SMT-LIB terms, e.g. $eo_mk_binary
    case TermKind::SMT_TO_EO_PROGRAM: ss << "SMT_TO_EO_PROGRAM"; break;
    // An operator that operates on native SMT-LIB terms, e.g. $sm_mk_pow2
    case TermKind::SMT_PROGRAM: ss << "SMT_PROGRAM"; break;
    case TermKind::SMT_BUILTIN_PROGRAM: ss << "SMT_BUILTIN_PROGRAM"; break;
    case TermKind::INTERNAL: ss << "INTERNAL"; break;
    case TermKind::NONE: ss << "NONE"; break;
    default: ss << "?TermKind"; break;
  }
  return ss.str();
}

void SmtMetaReduce::bind(const std::string& name, const Expr& e)
{
  // TODO: this case can probably be dropped??
  if (name.compare(0, 4, "$eo_") == 0 && e.getKind() == Kind::LAMBDA)
  {
    Expr p = e;
    // dummy type
#if 0
    std::vector<Expr> argTypes;
    Assert (e[0].getKind()==Kind::TUPLE);
    if (e[0].getNumChildren()==0)
    {
      // TODO: define here??
      EO_FATAL() << "Cannot handle 0-arg define";
      return;
    }
    for (size_t i=0, nargs=e[0].getNumChildren(); i<nargs; i++)
    {
      Expr aa = e[0][i];
      argTypes.push_back(d_tc.getType(aa));
    }
    Expr body = e[1];
    Expr retType = d_tc.getType(body);
    Expr pt = d_state.mkProgramType(argTypes, retType);
    std::cout << "....make program " << name << " for define, prog type is " << pt << std::endl;
    // Expr pt = d_state.mkBuiltinType(Kind::LAMBDA);
    Expr tmp = d_state.mkSymbol(Kind::PROGRAM_CONST, name, pt);
#else
    Expr pt = d_state.mkBuiltinType(Kind::LAMBDA);
    Expr tmp = d_state.mkSymbol(Kind::CONST, name, pt);
#endif
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

void SmtMetaReduce::printEmbAtomic(const std::string& str,
                                   std::ostream& os,
                                   TermContextKind parent,
                                   TermContextKind child)
{
  if (parent == TermContextKind::EUNOIA && child != TermContextKind::EUNOIA)
  {
    std::stringstream osEnd;
    if (child == TermContextKind::SMT)
    {
      os << "(eo.SmtTerm ";
      osEnd << ")";
    }
    else if (child == TermContextKind::SMT_TYPE)
    {
      os << "(eo.SmtType ";
      osEnd << ")";
    }
    else if (child == TermContextKind::SMT_VALUE)
    {
      os << "(eo.SmtValue ";
      osEnd << ")";
    }
    else
    {
      EO_FATAL() << "Unknown target kind " << termContextKindToString(child);
    }
    // TODO: more error checking??
    os << str << osEnd.str();
  }
  else
  {
    os << str;
  }
}

void SmtMetaReduce::printEmbAtomicTerm(const Expr& c,
                                       std::ostream& os,
                                       TermContextKind parent)
{
#ifdef NEW_DEF
  Kind k = c.getKind();
  if (k == Kind::TYPE)
  {
    os << "eo.Type";
    return;
  }
  std::string name;
  TermContextKind child = getMetaKind(c);
  if (child == TermContextKind::PROGRAM)
  {
    // programs always print verbatim
    os << c;
    return;
  }
  bool isSmtBuiltin = (parent == TermContextKind::SMT_BUILTIN);
  std::stringstream ss;
  std::stringstream ssEnd;
  if (k == Kind::CONST)
  {
    ss << termContextKindToPrefix(child) << c;
  }
  else if (k == Kind::BOOL_TYPE)
  {
    ss << "tsm.Bool";
  }
  else
  {
    const Literal* l = c.getValue()->asLiteral();
    if (l == nullptr)
    {
      EO_FATAL() << "Unknown atomic term kind " << k;
      return;
    }
    if (k == Kind::BOOLEAN)
    {
      if (!isSmtBuiltin)
      {
        ss << "sm.";
        ss << (l->d_bool ? "True" : "False");
      }
      else
      {
        ss << (l->d_bool ? "true" : "false");
      }
    }
    else if (k == Kind::NUMERAL)
    {
      if (!isSmtBuiltin)
      {
        ss << "(sm.Numeral ";
        ssEnd << ")";
      }
      const Integer& ci = l->d_int;
      if (ci.sgn() == -1)
      {
        const Integer& cin = -ci;
        ss << "(- " << cin.toString() << ")";
      }
      else
      {
        ss << ci.toString();
      }
    }
    else if (k == Kind::RATIONAL)
    {
      if (!isSmtBuiltin)
      {
        ss << "(sm.Rational ";
        ssEnd << ")";
      }
      ss << c;
    }
    else if (k == Kind::BINARY)
    {
      if (!isSmtBuiltin)
      {
        ss << "(sm.Binary";
        ssEnd << ")";
      }
      const BitVector& bv = l->d_bv;
      const Integer& bvi = bv.getValue();
      ss << bv.getSize() << " " << bvi.toString();
    }
    else if (k == Kind::STRING)
    {
      if (!isSmtBuiltin)
      {
        ss << "(sm.String ";
        ssEnd << ")";
      }
      ss << c;
    }
    else
    {
      EO_FATAL() << "Unknown atomic term literal kind " << k;
    }
  }
  ss << ssEnd.str();
  printEmbAtomic(ss.str(), os, parent, child);
#else
  // TODO: take inSmtTerm into account??
  std::string cname;
  TermKind tk = getTermKind(c, cname);
  Kind k = c.getKind();
  if (k == Kind::TYPE)
  {
    os << "eo.Type";
    return;
  }
  std::stringstream osEnd;
  if (isProgramKind(tk))
  {
    os << c;
    // std::cout << "program const: " << c << " " << d_eoTmpNil << " " <<
    // (c==d_eoTmpNil) << std::endl;
    return;
  }
  if (parent == TermContextKind::EUNOIA && !isEunoiaKind(tk))
  {
    // os << "; due to non-eunoia kind " << termKindToString(tk) << " for " <<
    // cname << std::endl;
    if (k == Kind::BOOL_TYPE)
    {
      // Builtin Eunoia types that are made into SMT-LIB types go here.
      os << "(eo.SmtType ";
    }
    else
    {
      os << "(eo.SmtTerm ";
    }
    osEnd << ")";
  }
  if (k == Kind::CONST)
  {
    if (tk == TermKind::INTERNAL)
    {
      os << cname;
    }
    else if (isEunoiaKind(tk))
    {
      os << "eo." << cname;
    }
    else if (tk == TermKind::SMT_TYPE_DT_CONS)
    {
      os << "tsm." << cname;
    }
    else
    {
      os << "sm." << cname;
    }
  }
  else if (k == Kind::BOOL_TYPE)
  {
    os << "tsm.Bool";
  }
  else
  {
    const Literal* l = c.getValue()->asLiteral();
    if (l == nullptr)
    {
      EO_FATAL() << "Unknown atomic term kind " << k;
      return;
    }
    if (k == Kind::BOOLEAN)
    {
      if (parent == TermContextKind::SMT_BUILTIN)
      {
        os << (l->d_bool ? "true" : "false");
      }
      else
      {
        os << "sm." << (l->d_bool ? "True" : "False");
      }
    }
    else if (k == Kind::NUMERAL)
    {
      if (parent == TermContextKind::SMT)
      {
        os << "(sm.Numeral ";
        osEnd << ")";
      }
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
    }
    else if (k == Kind::RATIONAL)
    {
      if (parent == TermContextKind::SMT)
      {
        os << "(sm.Rational ";
        osEnd << ")";
      }
      os << c;
    }
    else if (k == Kind::DECIMAL)
    {
      if (parent == TermContextKind::SMT)
      {
        os << "(sm.Decimal ";
        osEnd << ")";
      }
      os << c;
    }
    else if (k == Kind::BINARY || k == Kind::HEXADECIMAL)
    {
      if (parent == TermContextKind::SMT)
      {
        os << "(sm.";
        os << (k == Kind::BINARY ? "Binary " : "Hexadecimal ");
        osEnd << ")";
      }
      const BitVector& bv = l->d_bv;
      const Integer& bvi = bv.getValue();
      os << bv.getSize() << " " << bvi.toString();
    }
    else if (k == Kind::STRING)
    {
      if (parent == TermContextKind::SMT)
      {
        os << "(sm.String ";
        osEnd << ")";
      }
      os << c;
    }
    else
    {
      EO_FATAL() << "Unknown atomic term literal kind " << k;
    }
  }
  os << osEnd.str();
#endif
}

TermKind SmtMetaReduce::printEmbType(const Expr& c,
                                     std::ostream& os,
                                     TermContextKind tctx)
{
  Assert(!c.isNull());
  Expr t = c;
  if (c.getKind() == Kind::QUOTE_TYPE)
  {
    Expr qt = t[0];
    t = d_tc.getType(qt);
  }
#ifdef NEW_DEF
  if (c == d_metaEoTerm)
  {
    os << "eo.Term";
  }
  else if (c == d_metaSmtTerm)
  {
    os << "sm.Term";
  }
  else if (c == d_metaSmtType)
  {
    os << "sm.Type";
  }
  else if (c == d_metaSmtValue)
  {
    // os << "sm.Type";
  }
  return TermKind::NONE;
#else
  std::string name;
  std::vector<Expr> args;
  TermKind tk = getTermKind(t, name);
  if (tk == TermKind::SMT_BUILTIN_TYPE)
  {
    if (t.getNumChildren() == 2)
    {
      os << name;
    }
    else
    {
      // NOTE: could allow ground terms as arguments here
      // this would be necessary if model_smt.eo had concrete
      // instances of bitvectors.
      EO_FATAL() << "Cannot handle parametric builtin type " << c;
    }
  }
  else if (tk == TermKind::SMT_TERM_TYPE)
  {
    os << "sm.Term";
  }
  else if (tk == TermKind::SMT_TYPE_TYPE)
  {
    os << "tsm.Type";
  }
  else if (tk == TermKind::EUNOIA_TERM_TYPE || tk == TermKind::EUNOIA_TERM
           || tk == TermKind::EUNOIA_TYPE_TYPE || tk == TermKind::EUNOIA_BOOL)
  {
    os << "eo.Term";
  }
  else if (tk == TermKind::SMT_TERM)
  {
    // a user provided specification of a type???
    os << "eo.Term";
  }
  else
  {
    // TODO: check for bad types
    // os << "eo.Term";
    EO_FATAL() << "Unexpected printEmbType in " << t << ", kind is "
               << termKindToString(tk);
  }
  return tk;
#endif
}

bool SmtMetaReduce::printEmbPatternMatch(const Expr& c,
                                         const std::string& initCtx,
                                         std::ostream& os,
                                         SelectorCtx& ctx,
                                         size_t& nconj,
                                         TermContextKind tinit)
{
#ifdef NEW_DEF
  tinit = tinit == TermContextKind::NONE ? TermContextKind::EUNOIA : tinit;
  // third tuple is a context which indicates the final SMT
  // type we are printing (eo.Term vs. sm.Term)
  std::map<Expr, std::string>::iterator it;
  std::vector<std::tuple<Expr, std::string, TermContextKind>> visit;
  std::tuple<Expr, std::string, TermContextKind> cur;
  Expr ctmp = c;
  visit.emplace_back(c, initCtx, tinit);
  ConjPrint print;
  do
  {
    cur = visit.back();
    visit.pop_back();
    Expr tcur = std::get<0>(cur);
    std::string currTerm = std::get<1>(cur);
    TermContextKind tkctx = std::get<2>(cur);
    Kind ck = tcur.getKind();
    std::stringstream cname;
    bool printArgs = false;
    size_t printArgStart = 0;
    std::cout << "  pm: " << tcur << " / " << currTerm << " / "
              << termContextKindToString(tkctx) << std::endl;
    if (ck == Kind::APPLY && isProgram(tcur[0]))
    {
      EO_FATAL() << "Cannot match on program " << tcur[0];
    }
    if (ck == Kind::APPLY)
    {
      Assert(tcur.getNumChildren() == 2);
      // Determine if this is a Eunoia internal term, or an
      // SMT term eagerly here
      std::string smConsName;
      std::cout << "  atk: " << tcur[0] << std::endl;
      TermContextKind atk = getMetaKind(tcur);
      std::cout << "  atk: " << tcur[0] << " is "
                << termContextKindToString(atk) << std::endl;
      // if the Eunoia term is an SMT term, change the context
      // and use the eo.SmtTerm selector
      if (tkctx == TermContextKind::EUNOIA && atk != TermContextKind::EUNOIA)
      {
        Assert(atk == TermContextKind::SMT || atk == TermContextKind::SMT_TYPE
               || atk == TermContextKind::SMT_VALUE);
        std::string cons = termContextKindToCons(atk);
        std::stringstream tester;
        tester << "((_ is eo." << cons << ") " << currTerm << ")";
        print.push(tester.str());
        std::stringstream sssn;
        sssn << "(eo." << cons << ".arg1 " << currTerm << ")";
        currTerm = sssn.str();
        // our context is now updated
        tkctx = atk;
      }
      // Use the appropriate prefix
      cname << termContextKindToPrefix(tkctx) << "Apply";
      printArgs = true;
    }
    else if (ck == Kind::FUNCTION_TYPE)
    {
      // TODO: can this occur?
      // maybe if reasoning about function as first class argument?
      cname << termContextKindToPrefix(tkctx) << "FunType";
      printArgs = true;
    }
    else if (ck == Kind::APPLY_OPAQUE)
    {
      // will use a tester
      printEmbAtomicTerm(tcur[0], cname, TermContextKind::NONE);
      printArgStart = 1;
      printArgs = true;
      // we don't know the context of children, we compute per child below
      tkctx = TermContextKind::NONE;
    }
    if (printArgs)
    {
      // argument must be an apply
      std::stringstream tester;
      tester << "((_ is " << cname.str() << ") " << currTerm << ")";
      print.push(tester.str());
      for (size_t i = printArgStart, nchild = tcur.getNumChildren(); i < nchild;
           i++)
      {
        TermContextKind tcc = tkctx;
        if (tcc == TermContextKind::NONE)
        {
          // must compute it from the child
          Expr cc = tcur[i];
          Expr ccType = d_tc.getType(cc);
          if (ccType == d_metaEoTerm)
          {
            tcc = TermContextKind::EUNOIA;
          }
          else if (ccType == d_metaSmtTerm)
          {
            tcc = TermContextKind::SMT;
          }
          else if (ccType == d_metaSmtType)
          {
            tcc = TermContextKind::SMT_TYPE;
          }
          else
          {
            // otherwise assume builtin
            tcc = TermContextKind::SMT_BUILTIN;
          }
        }
        std::stringstream ssNext;
        ssNext << "(" << cname.str() << ".arg" << (i + 1 - printArgStart) << " "
               << currTerm << ")";
        // the next type is "reset"
        visit.emplace_back(tcur[i], ssNext.str(), tkctx);
      }
    }
    else if (ck == Kind::PARAM)
    {
      it = ctx.d_ctx.find(tcur);
      if (it == ctx.d_ctx.end())
      {
        // find time seeing this parameter, it is bound to the selector chain
        ctx.d_ctx[tcur] = currTerm;
        ctx.d_tctx[tcur] = tkctx;
      }
      else
      {
        // two occurrences of the same variable in a pattern
        // turns into an equality
        std::stringstream eq;
        eq << "(= " << currTerm << " " << it->second << ")";
        print.push(eq.str());
      }
    }
    else
    {
      // base case, use equality
      std::stringstream atomTerm;
      printEmbAtomicTerm(tcur, atomTerm, tkctx);
      std::stringstream eq;
      eq << "(= " << currTerm << " " << atomTerm.str() << ")";
      print.push(eq.str());
    }
  } while (!visit.empty());
  return true;
#else
  tinit = tinit == TermContextKind::NONE ? TermContextKind::EUNOIA : tinit;
  // third tuple is a context which indicates the final SMT
  // type we are printing (eo.Term vs. sm.Term)
  std::map<Expr, std::string>::iterator it;
  std::vector<std::tuple<Expr, std::string, TermContextKind, Expr>> visit;
  std::tuple<Expr, std::string, TermContextKind, Expr> cur;
  Expr ctmp = c;
  Expr tc = d_tc.getType(ctmp);
  visit.emplace_back(c, initCtx, tinit, tc);
  do
  {
    cur = visit.back();
    visit.pop_back();
    Expr tcur = std::get<0>(cur);
    std::string currTerm = std::get<1>(cur);
    TermContextKind tkctx = std::get<2>(cur);
    Expr curType = std::get<3>(cur);
    Kind ck = tcur.getKind();
    std::stringstream cname;
    bool printArgs = false;
    size_t printArgStart = 0;
    std::cout << "  pm: " << tcur << " / " << currTerm << " / "
              << termContextKindToString(tkctx) << std::endl;
    Expr nextType = curType;
    if (ck == Kind::APPLY && isProgram(tcur[0]))
    {
      EO_FATAL() << "Cannot match on program " << tcur[0];
    }
    if (ck == Kind::APPLY)
    {
      Assert(tcur.getNumChildren() == 2);
      // Determine if this is a Eunoia internal term, or an
      // SMT term
      std::string smConsName;
      std::cout << "  atk: " << tcur[0] << std::endl;
      TermKind atk = getTermKind(tcur[0]);
      std::cout << "  atk: " << tcur[0] << " is " << termKindToString(atk)
                << std::endl;
      // if the Eunoia term is an SMT term, change the context
      // and use the eo.SmtTerm selector
      // FIXME: context switch for SMT_TYPE
      if (tkctx == TermContextKind::EUNOIA && atk == TermKind::SMT_TERM)
      {
        // changes context
        os << (nconj > 0 ? " " : "") << "((_ is eo.SmtTerm) " << currTerm
           << ")";
        nconj++;
        std::stringstream sssn;
        sssn << "(eo.SmtTerm.arg1 " << currTerm << ")";
        currTerm = sssn.str();
        cname << "sm.Apply";
        tkctx = TermContextKind::SMT;
      }
      else
      {
        // If we are an SMT apply, use sm. else eo.
        cname << (tkctx == TermContextKind::SMT ? "sm" : "eo") << ".Apply";
      }
      printArgs = true;
    }
    else if (ck == Kind::FUNCTION_TYPE)
    {
      // TODO: can this occur?
      // maybe if reasoning about function as first class argument?
      cname << (tkctx == TermContextKind::SMT ? "sm" : "eo") << ".FunType";
      printArgs = true;
    }
    else if (ck == Kind::APPLY_OPAQUE)
    {
      // will use a tester
      printEmbAtomicTerm(tcur[0], cname, tkctx);
      printArgStart = 1;
      printArgs = true;
      TermKind atk = getTermKind(tcur[0]);
      std::cout << "  atk-o: " << tcur[0] << " is " << termKindToString(atk)
                << std::endl;
      if (tkctx == TermContextKind::EUNOIA && atk == TermKind::EUNOIA_DT_CONS)
      {
        // the type of the Eunoia SMT-LIB constructor is SMT terms
        tkctx = TermContextKind::SMT;
      }
      if (tkctx == TermContextKind::SMT
          && (atk == TermKind::SMT_DT_CONS
              || atk == TermKind::SMT_TYPE_DT_CONS))
      {
        // the opaque arguments of SMT-LIB literal terms are builtin SMT terms
        // the opaque arguments of SMT-LIB types (e.g. uninterpreted sorts) are
        // also builtins
        tkctx = TermContextKind::SMT_BUILTIN;
      }
    }
    if (printArgs)
    {
      // argument must be an apply
      os << (nconj > 0 ? " " : "") << "((_ is " << cname.str() << ") "
         << currTerm << ")";
      nconj++;
      for (size_t i = printArgStart, nchild = tcur.getNumChildren(); i < nchild;
           i++)
      {
        std::stringstream ssNext;
        ssNext << "(" << cname.str() << ".arg" << (i + 1 - printArgStart) << " "
               << currTerm << ")";
        // the next type is "reset"
        Expr tcc = tcur[i];
        Expr nextType = d_tc.getType(tcc);
        visit.emplace_back(tcur[i], ssNext.str(), tkctx, nextType);
      }
    }
    else if (ck == Kind::PARAM)
    {
      it = ctx.d_ctx.find(tcur);
      if (it == ctx.d_ctx.end())
      {
        // find time seeing this parameter, it is bound to the selector chain
        ctx.d_ctx[tcur] = currTerm;
        ctx.d_tctx[tcur] = tkctx;
        // remember the type
        ctx.d_typeMatch[tcur] = curType;
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
      printEmbAtomicTerm(tcur, atomTerm, tkctx);
      os << (nconj > 0 ? " " : "") << "(= " << currTerm << " " << atomTerm.str()
         << ")";
      nconj++;
    }
  } while (!visit.empty());
  return true;
#endif
}

bool SmtMetaReduce::printEmbTerm(const Expr& body,
                                 std::ostream& os,
                                 const SelectorCtx& ctx,
                                 TermContextKind tinit)
{
#ifdef NEW_DEF
  std::map<Expr, std::string>::const_iterator it;
  std::map<Expr, TermContextKind>::const_iterator ittc;
  std::stringstream osEnd;
  std::vector<Expr> ll;
  // maps smt apply terms to the tuple that they actually are
  std::map<std::pair<Expr, TermContextKind>, TermContextKind> tctxChildren;
  std::map<std::pair<Expr, TermContextKind>, size_t> cparen;
  std::map<std::pair<Expr, TermContextKind>, TermContextKind>::iterator itt;
  Expr t = body;
  std::map<Expr, size_t>::iterator itv;
  std::vector<std::tuple<Expr, size_t, TermContextKind>> visit;
  std::tuple<Expr, size_t, TermContextKind> cur;
  Expr recTerm;
  tinit = tinit == TermContextKind::NONE ? TermContextKind::EUNOIA : tinit;
  visit.emplace_back(t, 0, tinit);
  do
  {
    cur = visit.back();
    recTerm = std::get<0>(cur);
    // we use "null" for a space
    if (recTerm.isNull())
    {
      os << " ";
      visit.pop_back();
      continue;
    }
    size_t childIndex = std::get<1>(cur);
    TermContextKind tkctx = std::get<2>(cur);
    std::pair<Expr, TermContextKind> key(recTerm, tkctx);
    // maybe its children have a different context?
    itt = tctxChildren.find(key);
    if (itt != tctxChildren.end())
    {
      tkctx = itt->second;
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
        ittc = ctx.d_tctx.find(recTerm);
        Assert(it != ctx.d_ctx.end()) << "Cannot find " << recTerm;
        // if it was matched in an SMT context, and this is a Eunoia context,
        // wrap it
        if (tkctx == TermContextKind::EUNOIA
            && ittc->second == TermContextKind::SMT)
        {
          os << "(eo.SmtTerm " << it->second << ")";
        }
        else
        {
          os << it->second;
        }
        visit.pop_back();
        continue;
      }
      else if (recTerm.getNumChildren() == 0)
      {
        printEmbAtomicTerm(recTerm, os, tkctx);
        visit.pop_back();
        continue;
      }
      TermContextKind newCtx = TermContextKind::NONE;
      if (ck == Kind::APPLY)
      {
        TermKind atk = getTermKind(recTerm[0]);
        std::cout << "tk: head of apply " << key.first << " : "
                  << termKindToString(atk) << " in ctx "
                  << termContextKindToString(tkctx) << std::endl;
        // all other operators always print as applications
        os << "(";
        cparen[key] = 1;
        if (atk == TermKind::PROGRAM)
        {
          newCtx = TermContextKind::EUNOIA;
        }
        else if (atk == TermKind::SMT_TO_EO_PROGRAM)
        {
          newCtx = TermContextKind::SMT;
        }
        else if (atk == TermKind::SMT_BUILTIN_PROGRAM)
        {
          newCtx = TermContextKind::SMT_BUILTIN;
          // do not print apply
        }
        else if (atk == TermKind::SMT_PROGRAM)
        {
          // TODO: meta kind here
          newCtx = TermContextKind::SMT;
        }
        else if (atk == TermKind::SMT_TERM && tkctx == TermContextKind::EUNOIA)
        {
          std::cout << "...change context to SMT_TERM" << std::endl;
          os << "eo.SmtTerm (sm.Apply ";
          // our children are now each SMT terms.
          Assert(recTerm.getNumChildren() == 2)
              << "Not 2 child apply SMT term: " << recTerm << " "
              << recTerm.getNumChildren();
          tkctx = TermContextKind::SMT;
          tctxChildren[key] = tkctx;
          cparen[key]++;
        }
        else if (atk == TermKind::EUNOIA_TERM || atk == TermKind::SMT_TERM)
        {
          Assert(recTerm.getNumChildren() == 2);
          // could use macro to ensure "Stuck" propagates
          // NOTE: if we have the invariant that we pattern matched, we don't
          // need to check
          os << (tkctx == TermContextKind::EUNOIA ? "$eo_Apply " : "sm.Apply ");
          // term context does not change
        }
        else
        {
          EO_FATAL() << "Unhandled term kind for " << recTerm << " "
                     << termKindToString(atk) << ", in context "
                     << termContextKindToString(tkctx);
        }
      }
      else
      {
        if (ck == Kind::APPLY_OPAQUE)
        {
          // this is always printed in the original context first??
          std::string sname;
          TermKind atk = getTermKind(recTerm, sname);
          std::cout << "tk: apply opaque " << recTerm << " : "
                    << termKindToString(atk) << " in ctx "
                    << termContextKindToString(tkctx) << std::endl;
          if (tkctx == TermContextKind::EUNOIA
              && atk == TermKind::EUNOIA_DT_CONS)
          {
            // the arugment of eo.SmtTerm is an SMT term
            newCtx = TermContextKind::SMT;
          }
          else if (tkctx == TermContextKind::SMT
                   && atk == TermKind::SMT_DT_CONS)
          {
            // the opaque arguments of SMT-LIB literal constructors are builtin
            // SMT terms
            newCtx = TermContextKind::SMT_BUILTIN;
          }
          else if (atk == TermKind::SMT_BUILTIN_APPLY
                   || atk == TermKind::SMT_BUILTIN_TYPE
                   || atk == TermKind::SMT_STD_TYPE)
          {
            if (atk == TermKind::SMT_BUILTIN_APPLY)
            {
              tctxChildren[key] = TermContextKind::SMT_BUILTIN;
            }
            else if (atk == TermKind::SMT_BUILTIN_TYPE)
            {
              // The kind of subterms to appear in types (beneath $smt_type_*)
              tctxChildren[key] = TermContextKind::SMT_TYPE;
            }
            else
            {
              os << "tsm.";
              tctxChildren[key] = TermContextKind::SMT_BUILTIN;
              continue;
            }
            // this handles the corner case that ($smt_apply_0 "true") should
            // print as "true" not "(true)".
            if (recTerm.getNumChildren() > 2)
            {
              os << "(";
              cparen[key] = 1;
            }
            // the first argument is the opaque operator,
            // the second argument is taken as a name
            std::get<1>(visit.back())++;
            std::get<1>(visit.back())++;
            os << sname;
            continue;
          }
          // all other operators print as applications
          os << "(";
          cparen[key] = 1;
        }
        else if (ck == Kind::FUNCTION_TYPE)
        {
          Assert(recTerm.getNumChildren() == 2);
          // must use macro to ensure "Stuck" propagates
          os << "($eo_FunType ";
          cparen[key] = 1;
        }
        else if (isLiteralOp(ck))
        {
          std::string kstr = kindToTerm(ck);
          if (kstr.compare(0, 4, "eo::") == 0)
          {
            os << "($eo_" << kstr.substr(4) << " ";
            cparen[key] = 1;
          }
          else
          {
            EO_FATAL() << "Bad name for literal kind " << ck << std::endl;
          }
        }
        else
        {
          EO_FATAL() << "Unhandled kind in print term " << ck << " " << recTerm
                     << " / " << termContextKindToString(tkctx) << std::endl;
        }
      }
      if (newCtx != TermContextKind::NONE)
      {
        tkctx = newCtx;
        tctxChildren[key] = newCtx;
      }
      Assert(recTerm[childIndex].getKind() != Kind::TUPLE);
      std::get<1>(visit.back())++;
      visit.emplace_back(recTerm[childIndex], 0, tkctx);
    }
    else if (childIndex >= recTerm.getNumChildren())
    {
      // done with arguments, close the appropriate number of parentheses
      for (size_t i = 0, ncparen = cparen[key]; i < ncparen; i++)
      {
        os << ")";
      }
      visit.pop_back();
    }
    else
    {
      // another argument
      Assert(childIndex < recTerm.getNumChildren());
      os << " ";
      std::get<1>(visit.back())++;
      visit.emplace_back(recTerm[childIndex], 0, tkctx);
    }
  } while (!visit.empty());
  return true;
#else
  // os << ctx.d_letBegin.str();
  std::map<Expr, std::string>::const_iterator it;
  std::map<Expr, TermContextKind>::const_iterator ittc;
  std::stringstream osEnd;
  std::vector<Expr> ll;
  // maps smt apply terms to the tuple that they actually are
  std::map<std::pair<Expr, TermContextKind>, TermContextKind> tctxChildren;
  std::map<std::pair<Expr, TermContextKind>, size_t> cparen;
  std::map<std::pair<Expr, TermContextKind>, TermContextKind>::iterator itt;
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
  */
  Expr t = body;
  std::map<Expr, size_t>::iterator itv;
  std::vector<std::tuple<Expr, size_t, TermContextKind>> visit;
  std::tuple<Expr, size_t, TermContextKind> cur;
  Expr recTerm;
  tinit = tinit == TermContextKind::NONE ? TermContextKind::EUNOIA : tinit;
  visit.emplace_back(t, 0, tinit);
  do
  {
    cur = visit.back();
    recTerm = std::get<0>(cur);
    // we use "null" for a space
    if (recTerm.isNull())
    {
      os << " ";
      visit.pop_back();
      continue;
    }
    size_t childIndex = std::get<1>(cur);
    TermContextKind tkctx = std::get<2>(cur);
    std::pair<Expr, TermContextKind> key(recTerm, tkctx);
    // maybe its children have a different context?
    itt = tctxChildren.find(key);
    if (itt != tctxChildren.end())
    {
      tkctx = itt->second;
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
        ittc = ctx.d_tctx.find(recTerm);
        Assert(it != ctx.d_ctx.end()) << "Cannot find " << recTerm;
        // if it was matched in an SMT context, and this is a Eunoia context,
        // wrap it
        if (tkctx == TermContextKind::EUNOIA
            && ittc->second == TermContextKind::SMT)
        {
          os << "(eo.SmtTerm " << it->second << ")";
        }
        else
        {
          os << it->second;
        }
        visit.pop_back();
        continue;
      }
      else if (recTerm.getNumChildren() == 0)
      {
        printEmbAtomicTerm(recTerm, os, tkctx);
        visit.pop_back();
        continue;
      }
      TermContextKind newCtx = TermContextKind::NONE;
      if (ck == Kind::APPLY)
      {
        TermKind atk = getTermKind(recTerm[0]);
        std::cout << "tk: head of apply " << key.first << " : "
                  << termKindToString(atk) << " in ctx "
                  << termContextKindToString(tkctx) << std::endl;
        // all other operators always print as applications
        os << "(";
        cparen[key] = 1;
        if (atk == TermKind::PROGRAM)
        {
          newCtx = TermContextKind::EUNOIA;
        }
        else if (atk == TermKind::SMT_TO_EO_PROGRAM)
        {
          newCtx = TermContextKind::SMT;
        }
        else if (atk == TermKind::SMT_BUILTIN_PROGRAM)
        {
          newCtx = TermContextKind::SMT_BUILTIN;
          // do not print apply
        }
        else if (atk == TermKind::SMT_PROGRAM)
        {
          // TODO: meta kind here
          newCtx = TermContextKind::SMT;
        }
        else if (atk == TermKind::SMT_TERM && tkctx == TermContextKind::EUNOIA)
        {
          std::cout << "...change context to SMT_TERM" << std::endl;
          os << "eo.SmtTerm (sm.Apply ";
          // our children are now each SMT terms.
          Assert(recTerm.getNumChildren() == 2)
              << "Not 2 child apply SMT term: " << recTerm << " "
              << recTerm.getNumChildren();
          tkctx = TermContextKind::SMT;
          tctxChildren[key] = tkctx;
          cparen[key]++;
        }
        else if (atk == TermKind::EUNOIA_TERM || atk == TermKind::SMT_TERM)
        {
          Assert(recTerm.getNumChildren() == 2);
          // could use macro to ensure "Stuck" propagates
          // NOTE: if we have the invariant that we pattern matched, we don't
          // need to check
          os << (tkctx == TermContextKind::EUNOIA ? "$eo_Apply " : "sm.Apply ");
          // term context does not change
        }
        else
        {
          EO_FATAL() << "Unhandled term kind for " << recTerm << " "
                     << termKindToString(atk) << ", in context "
                     << termContextKindToString(tkctx);
        }
      }
      else
      {
        if (ck == Kind::APPLY_OPAQUE)
        {
          // this is always printed in the original context first??
          std::string sname;
          TermKind atk = getTermKind(recTerm, sname);
          std::cout << "tk: apply opaque " << recTerm << " : "
                    << termKindToString(atk) << " in ctx "
                    << termContextKindToString(tkctx) << std::endl;
          if (tkctx == TermContextKind::EUNOIA
              && atk == TermKind::EUNOIA_DT_CONS)
          {
            // the arugment of eo.SmtTerm is an SMT term
            newCtx = TermContextKind::SMT;
          }
          else if (tkctx == TermContextKind::SMT
                   && atk == TermKind::SMT_DT_CONS)
          {
            // the opaque arguments of SMT-LIB literal constructors are builtin
            // SMT terms
            newCtx = TermContextKind::SMT_BUILTIN;
          }
          else if (atk == TermKind::SMT_BUILTIN_APPLY
                   || atk == TermKind::SMT_BUILTIN_TYPE
                   || atk == TermKind::SMT_STD_TYPE)
          {
            if (atk == TermKind::SMT_BUILTIN_APPLY)
            {
              tctxChildren[key] = TermContextKind::SMT_BUILTIN;
            }
            else if (atk == TermKind::SMT_BUILTIN_TYPE)
            {
              // The kind of subterms to appear in types (beneath $smt_type_*)
              tctxChildren[key] = TermContextKind::SMT_TYPE;
            }
            else
            {
              os << "tsm.";
              tctxChildren[key] = TermContextKind::SMT_BUILTIN;
              continue;
            }
            // this handles the corner case that ($smt_apply_0 "true") should
            // print as "true" not "(true)".
            if (recTerm.getNumChildren() > 2)
            {
              os << "(";
              cparen[key] = 1;
            }
            // the first argument is the opaque operator,
            // the second argument is taken as a name
            std::get<1>(visit.back())++;
            std::get<1>(visit.back())++;
            os << sname;
            continue;
          }
          // all other operators print as applications
          os << "(";
          cparen[key] = 1;
        }
        else if (ck == Kind::FUNCTION_TYPE)
        {
          Assert(recTerm.getNumChildren() == 2);
          // must use macro to ensure "Stuck" propagates
          os << "($eo_FunType ";
          cparen[key] = 1;
        }
        else if (isLiteralOp(ck))
        {
          std::string kstr = kindToTerm(ck);
          if (kstr.compare(0, 4, "eo::") == 0)
          {
            os << "($eo_" << kstr.substr(4) << " ";
            cparen[key] = 1;
          }
          else
          {
            EO_FATAL() << "Bad name for literal kind " << ck << std::endl;
          }
        }
        else
        {
          EO_FATAL() << "Unhandled kind in print term " << ck << " " << recTerm
                     << " / " << termContextKindToString(tkctx) << std::endl;
        }
      }
      if (newCtx != TermContextKind::NONE)
      {
        // TODO: improve??
        tkctx = newCtx;
        tctxChildren[key] = newCtx;
      }
      Assert(recTerm[childIndex].getKind() != Kind::TUPLE);
      std::get<1>(visit.back())++;
      visit.emplace_back(recTerm[childIndex], 0, tkctx);
    }
    else if (childIndex >= recTerm.getNumChildren())
    {
      // done with arguments, close the appropriate number of parentheses
      for (size_t i = 0, ncparen = cparen[key]; i < ncparen; i++)
      {
        os << ")";
      }
      visit.pop_back();
    }
    else
    {
      // another argument
      Assert(childIndex < recTerm.getNumChildren());
      os << " ";
      std::get<1>(visit.back())++;
      visit.emplace_back(recTerm[childIndex], 0, tkctx);
    }
  } while (!visit.empty());
  return true;
#endif
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
      std::cout << "WARNING: lambda " << p.first << std::endl;
      Expr e = p.second;
      TermKind tk = getTermKind(p.first);
      // things that are manually axiomatized
      if (tk == TermKind::INTERNAL)
      {
        continue;
      }
#if 0
      Assert(e[0].getKind() == Kind::TUPLE);
      std::vector<Expr> appChildren;
      appChildren.push_back(p.first);
      for (size_t i=0, nargs=e[0].getNumChildren(); i<nargs; i++)
      {
        appChildren.push_back(e[0][i]);
      }
      Expr progApp = d_state.mkExprSimple(Kind::APPLY, appChildren);
      Expr pcase = d_state.mkPair(progApp, e[1]);
      Expr prog = d_state.mkExprSimple(Kind::PROGRAM, {pcase});
      std::cout << "...do program " << p.first << " / " << prog << " instead" << std::endl;
      finalizeProgram(p.first, prog);
      std::cout << "...finished lambda program" << std::endl;
      return;
#endif
      // TODO: reduce to program immediately
      // prints as a define-fun
      d_defs << "; define " << p.first << std::endl;
      d_defs << "(define-fun " << p.first << " (";
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
        d_defs << "(" << vname.str() << " ";
        Expr argType = d_tc.getType(v);
        Assert(!argType.isNull());
        //
        printEmbType(argType, d_defs);
        d_defs << ")";
        ctx.d_ctx[v] = vname.str();
      }
      d_defs << ") ";
      Expr body = e[1];
      Expr retType = d_tc.getType(body);
      // determine the intial context for printing the term here
      // this ensures the body is printed as the appropriate type.
      TermContextKind ctxInit;
      if (retType.isNull())
      {
        // some programs don't technically type check??? introduced in
        // desugaring
        d_defs << "eo.Term";
        ctxInit = TermContextKind::NONE;
      }
      else
      {
        Assert(!retType.isNull()) << "Program " << p.first
                                  << " doesnt type check, in finalizeProgram";
        TermKind tk = printEmbType(retType, d_defs);
        ctxInit = termKindToContext(tk);
      }
      d_defs << " ";
      printEmbTerm(e[1], d_defs, ctx, ctxInit);
      // we now know the types of terms, take that into account
      d_defs << ")" << std::endl << std::endl;
      continue;
    }
    finalizeProgram(p.first, p.second);
  }
  d_progSeen.clear();
}

TermContextKind SmtMetaReduce::termKindToContext(TermKind tk)
{
  switch (tk)
  {
    case TermKind::SMT_BUILTIN_TYPE: return TermContextKind::SMT_BUILTIN;
    case TermKind::SMT_TERM:
    case TermKind::SMT_TERM_TYPE: return TermContextKind::SMT;
    case TermKind::SMT_TYPE_TYPE: return TermContextKind::SMT_TYPE;
    case TermKind::EUNOIA_TERM_TYPE:
    case TermKind::EUNOIA_TYPE_TYPE:
    case TermKind::EUNOIA_BOOL:
    case TermKind::EUNOIA_TERM: return TermContextKind::EUNOIA;
    default: EO_FATAL() << "unknown type " << termKindToString(tk); break;
  }
  return TermContextKind::NONE;
}
void SmtMetaReduce::finalizeProgram(const Expr& v, const Expr& prog)
{
  TermKind tk = getTermKind(v);
  // things that are manually axiomatized
  if (tk == TermKind::INTERNAL)
  {
    return;
  }
  std::cout << "Finalize program " << v << std::endl;
  d_defs << "; " << (prog.isNull() ? "fwd-decl: " : "program: ") << v
         << std::endl;
  std::stringstream decl;
  Expr vv = v;
  Expr vt = d_tc.getType(vv);
  decl << "(declare-fun " << v << " (";
  std::stringstream varList;
  Assert(vt.getKind() == Kind::PROGRAM_TYPE)
      << "bad type " << vt << " for " << v;
  size_t nargs = vt.getNumChildren();
  Assert(nargs > 1);
  std::vector<std::string> args;
  std::stringstream appTerm;
  appTerm << "(" << v;
  std::stringstream stuckCases;
  size_t nstuckCond = 0;
  std::vector<TermKind> termKindsForTypeArgs;
  for (size_t i = 1; i < nargs; i++)
  {
    if (i > 1)
    {
      decl << " ";
      varList << " ";
    }
    std::stringstream argType;
    TermKind tka = printEmbType(vt[i - 1], argType);
    // d_defs << "; defs: " << vt[i - 1] << " is " << termKindToString(tka) <<
    // std::endl;
    decl << argType.str();
    std::stringstream ssArg;
    ssArg << "x" << i;
    appTerm << " " << ssArg.str();
    args.emplace_back(ssArg.str());
    varList << "(" << ssArg.str() << " " << argType.str() << ")";
    // don't have to check stuckness if type is not Eunoia
    if (tka == TermKind::EUNOIA_TYPE_TYPE || tka == TermKind::EUNOIA_TERM_TYPE
        || tka == TermKind::EUNOIA_BOOL || tka == TermKind::EUNOIA_TYPE_TYPE)
    {
      if (nstuckCond > 0)
      {
        stuckCases << " ";
      }
      nstuckCond++;
      stuckCases << "(= " << ssArg.str() << " eo.Stuck)";
    }
    termKindsForTypeArgs.push_back(tka);
  }
  std::stringstream stuckCond;
  if (nstuckCond > 1)
  {
    stuckCond << "(or " << stuckCases.str() << ")";
  }
  else if (nstuckCond == 0)
  {
    stuckCond << "false";
  }
  else
  {
    stuckCond << stuckCases.str();
  }
  appTerm << ")";
  std::stringstream retType;
  TermKind retTypeCtx = printEmbType(vt[nargs - 1], retType);
  decl << ") " << retType.str() << ")" << std::endl;
  std::cout << "DECLARE " << decl.str() << std::endl;
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
  // start with stuck case, if not a SMT program
  bool isEoProg =
      (tk != TermKind::SMT_BUILTIN_PROGRAM && tk != TermKind::SMT_TO_EO_PROGRAM
       && tk != TermKind::SMT_PROGRAM);
  if (isEoProg)
  {
    cases << "  (ite " << stuckCond.str() << std::endl;
    cases << "    eo.Stuck" << std::endl;
    casesEnd << ")";
  }
  size_t ncases = prog.getNumChildren();
  SelectorCtx ctx;
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
    ctx.clear();
    std::stringstream currCase;
    size_t nconj = 0;
    Assert(hd.getNumChildren() == nargs);
    for (size_t j = 1, nhdchild = hd.getNumChildren(); j < nhdchild; j++)
    {
      // print the pattern matching predicate for this argument, all
      // concatenated together
      std::cout << "Print pat matching for " << hd[j] << std::endl;
      // context depends on the kind of the argument
      TermContextKind ctxPatMatch =
          termKindToContext(termKindsForTypeArgs[j - 1]);
      printEmbPatternMatch(
          hd[j], args[j - 1], currCase, ctx, nconj, ctxPatMatch);
      std::cout << "...returns " << currCase.str() << std::endl;
    }
    // compile the return for this case
    std::stringstream currRet;
    TermContextKind bodyInitCtx = termKindToContext(retTypeCtx);
    std::cout << "...print " << body << " in context "
              << termContextKindToString(bodyInitCtx) << std::endl;
    printEmbTerm(body, currRet, ctx, bodyInitCtx);
    std::cout << "...finished" << std::endl;
    std::cout << "...result is " << currRet.str() << std::endl;
    if (isEoProg || tk == TermKind::SMT_PROGRAM)
    {
      // we permit SMT_PROGRAM and Eunoia programs to have pattern matching
      // now print the case/return
      // for SMT_PROGRAM, the last case is assumed to be total
      // this is part of the trusted core: to ensure all programs in
      // model_smt.eo are total.
      if (i + 1 < ncases || tk != TermKind::SMT_PROGRAM)
      {
        cases << "  (ite ";
        printConjunction(nconj, currCase.str(), cases, ctx);
        cases << std::endl;
        casesEnd << ")";
      }
      cases << "    " << currRet.str() << std::endl;
    }
    else
    {
      if (i > 0 && tk != TermKind::SMT_PROGRAM)
      {
        EO_FATAL()
            << "Program " << v
            << " is not a Eunoia program and thus cannot have multiple cases";
      }
      if (nconj > 0)
      {
        EO_FATAL() << "Program " << v
                   << " is not a Eunoia program and thus cannot rely on "
                      "pattern matching";
      }
      cases << "  " << currRet.str() << std::endl;
    }
  }
  // TODO:
  // now go back and print the variable list, now that we know the types
  // of the variables
  std::stringstream varListSafe, declSafe;
  // if there is only one case, we can do type inference
  if (ncases == 1)
  {
    // d_defs << std::endl << "; examine: " << v << std::endl;
    std::map<Expr, TermContextKind>::iterator itm;
    for (size_t i = 1; i < nargs; i++)
    {
      if (i > 1)
      {
        declSafe << " ";
        varListSafe << " ";
      }
      itm = ctx.d_tctx.find(vt[i - 1]);
      if (itm != ctx.d_tctx.end())
      {
        // d_defs << "; x" << i << " matched with " << itm->second << std::endl;
        // d_defs << "; x" << i << " matched in context " <<
        // termContextKindToString(itm->second) << std::endl;
      }
      std::stringstream argType;
      printEmbType(vt[i - 1], argType);
      declSafe << argType.str();
      std::stringstream ssArg;
      ssArg << "x" << i;
      varListSafe << "(" << ssArg.str() << " " << argType.str() << ")";
    }
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
    d_defs << "(define-fun " << v << " (" << varList.str() << ") "
           << retType.str() << std::endl;
  }
  d_defs << cases.str();
  if (isEoProg)
  {
    d_defs << "    eo.Stuck";
  }
  d_defs << casesEnd.str();
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
    std::cout << "BEGIN FINALIZE " << e << std::endl;
    std::string consName;
    TermKind tk = getTermKind(e, consName);
    // ignore deep embeddings of smt terms
    // all symbols beginning with @ are not part of term definition
    if (tk == TermKind::INTERNAL || tk == TermKind::SMT_TERM_TYPE
        || tk == TermKind::SMT_TYPE_TYPE || tk == TermKind::EUNOIA_TERM_TYPE
        || tk == TermKind::SMT_BUILTIN_PROGRAM || tk == TermKind::SMT_PROGRAM
        || tk == TermKind::SMT_TO_EO_PROGRAM || tk == TermKind::PROGRAM
        || tk == TermKind::SMT_BUILTIN_APPLY || tk == TermKind::SMT_BUILTIN_TYPE
        || tk == TermKind::EUNOIA_DT_CONS)
    {
      continue;
    }
    std::cout << "FINALIZE " << e << " " << termKindToString(tk) << std::endl;
    std::stringstream* out = nullptr;
    std::stringstream prefix;
    if (tk == TermKind::EUNOIA_TERM)  // tk == TermKind::EUNOIA_DT_CONS ||
    {
      prefix << "eo.";
      out = &d_eoTermDecl;
    }
    else if (tk == TermKind::SMT_TYPE_DT_CONS)
    {
      prefix << "tsm.";
      out = &d_typeDecl;
    }
    else
    {
      prefix << "sm.";
      out = &d_termDecl;
    }
    if (out == nullptr)
    {
      continue;
    }
    (*out) << "  ; declare " << consName << " " << termKindToString(tk)
           << std::endl;
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
    cname << prefix.str() << consName;
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
    std::vector<TermKind>& mts = d_metaType[e];
    for (size_t i = 0; i < nopqArgs; i++)
    {
      (*out) << " (" << cname.str();
      (*out) << ".arg" << (i + 1) << " ";
      // print its type using the utility,
      // which takes into account what the type is in the final embedding
      Expr typ = ct[i];
      if (ct[i].getKind() == Kind::QUOTE_TYPE)
      {
        Expr targ = ct[i][0];
        typ = d_tc.getType(targ);
      }
      std::stringstream sst;
      TermKind tk = printEmbType(typ, sst);
      //(*out) << "; Printing datatype argument type " << typ << " gives \"" <<
      // sst.str() << "\" " << termKindToString(tk) << std::endl;
      (*out) << sst.str();
      mts.push_back(tk);
      (*out) << ")";
    }
    (*out) << ")" << std::endl;
    // is it an SMT-LIB symbol????
    // std::stringstream ss;
    // ss << e;
    // std::string name = ss.str();
  }
  d_declSeen.clear();
}

void SmtMetaReduce::finalize()
{  // Here, we expect $eo_get_meta_type to be defined as a function in the
  // signature, which is an oracle for saying which datatype a term belongs
  // to in the deep embedding. We expect this program to be defined as well
  // as the names of the types.
  d_eoGetMetaKind = lookupVar("$eo_get_meta_type");
  d_metaEoTerm = lookupVar("$eo_Term");
  d_metaSmtTerm = lookupVar("$smt_Term");
  d_metaSmtType = lookupVar("$smt_Type");
  d_metaSmtValue = lookupVar("$smt_Value");
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
  ssi << s_plugin_path << "plugins/smt_meta/smt_meta.smt2";
  std::ifstream in(ssi.str());
  std::ostringstream ss;
  ss << in.rdbuf();
  std::string finalSm = ss.str();

  replace(finalSm, "$SM_TERM_DECL$", d_termDecl.str());
  replace(finalSm, "$SM_TYPE_DECL$", d_typeDecl.str());
  replace(finalSm, "$SM_EO_TERM_DECL$", d_eoTermDecl.str());
  replace(finalSm, "$SM_DEFS$", d_defs.str());
  replace(finalSm, "$SMT_VC$", d_smtVc.str());

  std::stringstream sso;
  sso << s_plugin_path << "plugins/smt_meta/smt_meta_gen.smt2";
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
      d_smtVc << "  (= (" << eosc << call.str() << ") (eo.SmtTerm sm.True)))";
    }
    else
    {
      d_smtVc << "(= " << eosc << " (eo.SmtTerm sm.True))";
    }
    d_smtVc << " :named sm.conjecture." << vv << ")";
    d_smtVc << ")" << std::endl;
    // std::cout << "...set target" << std::endl;
    return false;
  }
  return true;
}

TermKind SmtMetaReduce::getTermKindApply(const Expr& t,
                                         std::string& name,
                                         std::vector<Expr>& args)
{
  Expr cur = t;
  while (cur.getKind() == Kind::APPLY)
  {
    args.push_back(cur[1]);
    cur = cur[0];
  }
  TermKind tk = isSmtApply(cur);
  if (tk != TermKind::NONE)
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
    return tk;
  }
  std::cout << cur << " is not smt apply" << std::endl;
  args.clear();
  // otherwise proceed to atomic case
  return getTermKindAtomic(cur, name);
}

TermKind SmtMetaReduce::isSmtApply(const Expr& t)
{
  std::stringstream ss;
  ss << t;
  std::string sname = ss.str();
  if (sname.compare(0, 11, "$smt_apply_") == 0)
  {
    std::string sarity = sname.substr(11);
    // always add one
    return TermKind::SMT_BUILTIN_APPLY;
  }
  if (sname.compare(0, 10, "$smt_type_") == 0)
  {
    std::string sarity = sname.substr(10);
    // always add one
    return TermKind::SMT_BUILTIN_TYPE;
  }
  if (sname.compare(0, 14, "$smt_std_type_") == 0)
  {
    std::string sarity = sname.substr(14);
    // always add one
    return TermKind::SMT_STD_TYPE;
  }
  return TermKind::NONE;
}

TermKind SmtMetaReduce::getSafeTermKind(const Expr& e)
{
  Expr etmp = e;
  Expr typeE = d_tc.getType(etmp);
  std::cout << "TYPE " << typeE << std::endl;
  return TermKind::NONE;
}
TermKind SmtMetaReduce::getTermKind(const Expr& e)
{
  std::string name;
  return getTermKind(e, name);
}
TermKind SmtMetaReduce::getTermKind(const Expr& e, std::string& name)
{
  std::cout << "Get term kind " << e << " " << e.getKind() << std::endl;
  Expr cur = e;
  if (cur.getKind() == Kind::APPLY_OPAQUE)
  {
    // look at the operator
    std::stringstream ss;
    ss << cur[0];
    std::string sname = ss.str();
    TermKind tk = TermKind::NONE;
    if (sname.compare(0, 11, "$smt_apply_") == 0)
    {
      tk = TermKind::SMT_BUILTIN_APPLY;
    }
    else if (sname.compare(0, 10, "$smt_type_") == 0)
    {
      tk = TermKind::SMT_BUILTIN_TYPE;
    }
    else if (sname.compare(0, 8, "$smd_eo.") == 0)
    {
      name = sname.substr(8);
      return TermKind::EUNOIA_DT_CONS;
    }
    else if (sname.compare(0, 8, "$smd_sm.") == 0)
    {
      name = sname.substr(8);
      return TermKind::SMT_DT_CONS;
    }
    else if (sname.compare(0, 9, "$smd_tsm.") == 0)
    {
      name = sname.substr(9);
      return TermKind::SMT_TYPE_DT_CONS;
    }
    if (tk != TermKind::NONE)
    {
      if (cur.getNumChildren() <= 1)
      {
        EO_FATAL() << "Unexpected arity for opaque operator " << cur;
      }
      if (cur[1].getKind() != Kind::STRING)
      {
        EO_FATAL() << "Expected string for SMT-LIB app name, got " << sname;
      }
      const Literal* l = cur[1].getValue()->asLiteral();
      name = l->d_str.toString();
      return tk;
    }
    // otherwise look at its head
    cur = e[0];
  }
  else
  {
    while (cur.getKind() == Kind::APPLY)
    {
      cur = cur[0];
    }
  }
  return getTermKindAtomic(cur, name);
}

TermKind SmtMetaReduce::getTermKindAtomic(const Expr& e, std::string& name)
{
  if (e == d_eoGetMetaKind)
  {
    return TermKind::INTERNAL;
  }
  Kind k = e.getKind();
  std::stringstream ss;
  ss << e;
  std::string sname = ss.str();
  if (k == Kind::PROGRAM_CONST)
  {
    if (sname.compare(0, 7, "$sm_mk_") == 0)
    {
      name = sname;
      return TermKind::SMT_BUILTIN_PROGRAM;
    }
    if (sname.compare(0, 7, "$eo_mk_") == 0)
    {
      name = sname;
      return TermKind::SMT_TO_EO_PROGRAM;
    }
    if (sname.compare(0, 6, "$smtx_") == 0)
    {
      name = sname;
      return TermKind::SMT_PROGRAM;
    }
    return TermKind::PROGRAM;
  }
  else if (k == Kind::PARAM)
  {
    // parameters are Eunoia
    return TermKind::EUNOIA_TERM_TYPE;
  }
  else if (k == Kind::TYPE)
  {
    // Type in Eunoia
    return TermKind::EUNOIA_TYPE_TYPE;
  }
  else if (k == Kind::BOOL_TYPE)
  {
    return TermKind::EUNOIA_BOOL;
  }
  else if (k == Kind::QUOTE_TYPE)
  {
    return TermKind::EUNOIA_QUOTE_TYPE;
  }
  else if (isLiteral(k))
  {
    return TermKind::SMT_TERM;
  }
  else if (k != Kind::CONST)
  {
    Assert(!e.isNull());
    EO_FATAL() << "Unhandled kind " << k << " in getTermKindAtomic " << e;
    return TermKind::NONE;
  }
  // TODO: SMT_TERM_TYPE and EUNOIA_TERM_TYPE
  // can probably be "INTERNAL".
  if (sname.compare(0, 11, "$smt_apply_") == 0
      || sname.compare(0, 10, "$smt_type_") == 0)
  {
    name = sname;
    return TermKind::INTERNAL;
  }
  if (sname == "$smt_Term")
  {
    name = sname;
    return TermKind::SMT_TERM_TYPE;
  }
  if (sname == "$smt_Type")
  {
    name = sname;
    return TermKind::SMT_TYPE_TYPE;
  }
  if (sname == "$eo_Term")
  {
    name = sname;
    return TermKind::EUNOIA_TERM_TYPE;
  }
  if (sname.compare(0, 8, "$smd_eo.") == 0)
  {
    name = sname.substr(8);
    return TermKind::EUNOIA_DT_CONS;
  }
  else if (sname.compare(0, 8, "$smd_sm.") == 0)
  {
    name = sname.substr(8);
    return TermKind::SMT_DT_CONS;
  }
  else if (sname.compare(0, 9, "$smd_tsm.") == 0)
  {
    name = sname.substr(9);
    return TermKind::SMT_TYPE_DT_CONS;
  }
  // symbols that begin with @ are treated as Eunoia terms.
  if (sname.compare(0, 1, "@") == 0 || sname.compare(0, 8, "$eo_List") == 0)
  {
    name = sname;
    return TermKind::EUNOIA_TERM;
  }
  name = sname;
  return TermKind::SMT_TERM;
}

bool SmtMetaReduce::isProgram(const Expr& t)
{
  if (t.getKind() == Kind::PROGRAM_CONST)
  {
    return true;
  }
  TermKind tk = getTermKind(t);
  return isProgramKind(tk);
}
bool SmtMetaReduce::isProgramKind(TermKind tk)
{
  return tk == TermKind::SMT_BUILTIN_PROGRAM
         || tk == TermKind::SMT_TO_EO_PROGRAM || tk == TermKind::PROGRAM
         || tk == TermKind::SMT_PROGRAM;
}

TermContextKind SmtMetaReduce::getMetaKind(const Expr& e)
{
  std::map<Expr, TermContextKind>::iterator it = d_metaKind.find(e);
  if (it != d_metaKind.end())
  {
    return it->second;
  }

  Expr hd = e;
  // if an apply, we look for the head, this will determine eo.Apply vs.
  // sm.Apply
  while (hd.getKind() == Kind::APPLY)
  {
    hd = hd[0];
  }
  // check for programs
  TermContextKind tk = TermContextKind::NONE;
  if (hd.getKind() == Kind::PROGRAM_CONST)
  {
    tk = TermContextKind::PROGRAM;
  }
  else
  {
    Expr mapp = d_state.mkExprSimple(Kind::APPLY, {d_eoGetMetaKind, hd});
    Ctx ectx;
    Expr mm = d_tc.evaluate(mapp.getValue(), ectx);
    if (mm == d_metaEoTerm)
    {
      tk = TermContextKind::EUNOIA;
    }
    else if (mm == d_metaSmtTerm)
    {
      tk = TermContextKind::SMT;
    }
    else if (mm == d_metaSmtType)
    {
      tk = TermContextKind::SMT_TYPE;
    }
  }
  d_metaKind[e] = tk;
  return tk;
}

}  // namespace ethos
