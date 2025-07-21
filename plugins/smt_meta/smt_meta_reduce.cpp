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

ConjPrint::ConjPrint() : d_npush(0) {}
void ConjPrint::push(const std::string& str)
{
  if (d_npush > 0)
  {
    d_ss << " ";
  }
  d_ss << str;
  d_npush++;
}

void ConjPrint::printConjunction(std::ostream& os, bool isDisj)
{
  if (d_npush == 0)
  {
    os << (isDisj ? "false" : "true");
  }
  else if (d_npush > 1)
  {
    os << "(" << (isDisj ? "or" : "and") << " " << d_ss.str() << ")";
  }
  else
  {
    os << d_ss.str();
  }
}

SelectorCtx::SelectorCtx() {}
void SelectorCtx::clear()
{
  d_ctx.clear();
  d_tctx.clear();
}

SmtMetaReduce::SmtMetaReduce(State& s) : StdPlugin(s) {}

SmtMetaReduce::~SmtMetaReduce() {}

MetaKind prefixToMetaKind(const std::string& str)
{
  if (str == "eo")
  {
    return MetaKind::EUNOIA;
  }
  else if (str == "sm")
  {
    return MetaKind::SMT;
  }
  else if (str == "tsm")
  {
    return MetaKind::SMT_TYPE;
  }
  else if (str == "vsm")
  {
    return MetaKind::SMT_VALUE;
  }
  else if (str == "msm")
  {
    return MetaKind::SMT_MAP;
  }
  Assert(false) << "Bad prefix \"" << str << "\"";
  return MetaKind::NONE;
}

std::string metaKindToString(MetaKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case MetaKind::EUNOIA: ss << "EUNOIA"; break;
    case MetaKind::SMT: ss << "SMT"; break;
    case MetaKind::SMT_BUILTIN: ss << "SMT_BUILTIN"; break;
    case MetaKind::SMT_TYPE: ss << "SMT_TYPE"; break;
    case MetaKind::SMT_VALUE: ss << "SMT_VALUE"; break;
    case MetaKind::SMT_MAP: ss << "SMT_MAP"; break;
    case MetaKind::PROGRAM: ss << "PROGRAM"; break;
    case MetaKind::NONE: ss << "NONE"; break;
    default: ss << "?MetaKind"; break;
  }
  return ss.str();
}
std::string metaKindToPrefix(MetaKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case MetaKind::EUNOIA: ss << "eo."; break;
    case MetaKind::SMT: ss << "sm."; break;
    case MetaKind::SMT_TYPE: ss << "tsm."; break;
    case MetaKind::SMT_VALUE: ss << "vsm."; break;
    case MetaKind::SMT_BUILTIN: ss << "?"; break;
    default: ss << "?MetaKindPrefix_" << metaKindToString(k); break;
  }
  return ss.str();
}
std::string metaKindToCons(MetaKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case MetaKind::SMT: ss << "SmtTerm"; break;
    case MetaKind::SMT_TYPE: ss << "SmtType"; break;
    case MetaKind::SMT_VALUE: ss << "SmtValue"; break;
    default: ss << "?MetaKindCons"; break;
  }
  return ss.str();
}

bool SmtMetaReduce::printMetaType(const Expr& t,
                                  std::ostream& os,
                                  MetaKind tctx)
{
  MetaKind tk = getTypeMetaKind(t, tctx);
  switch (tk)
  {
    case MetaKind::EUNOIA: os << "eo.Term"; break;
    case MetaKind::SMT: os << "sm.Term"; break;
    case MetaKind::SMT_TYPE: os << "tsm.Type"; break;
    case MetaKind::SMT_VALUE: os << "vsm.Value"; break;
    case MetaKind::SMT_BUILTIN: os << getEmbedName(t); break;
    case MetaKind::SMT_MAP: os << "msm.Map"; break;
    default: return false;
  }
  return true;
}

void SmtMetaReduce::printEmbAtomicTerm(const Expr& c,
                                       std::ostream& os,
                                       MetaKind parent)
{
  parent = parent == MetaKind::NONE ? MetaKind::EUNOIA : parent;
  Kind k = c.getKind();
  if (k == Kind::TYPE)
  {
    os << "eo.Type";
    return;
  }
  std::string name;
  MetaKind child = getMetaKindReturn(c, parent);
  if (child == MetaKind::PROGRAM)
  {
    // programs always print verbatim
    os << c;
    return;
  }
  bool isSmtBuiltin = (parent == MetaKind::SMT_BUILTIN);
  std::stringstream osEnd;
  if (k == Kind::CONST)
  {
    std::string cname = getName(c);
    // if it is an explicit embedding of a datatype, take the suffix
    if (cname.compare(0, 5, "$smd_") == 0)
    {
      os << cname.substr(5);
    }
    else
    {
      os << metaKindToPrefix(child) << cname;
    }
  }
  else if (k == Kind::BOOL_TYPE)
  {
    // Bool is embedded as an SMT type, we have to wrap it explicitly here.
    if (parent == MetaKind::EUNOIA)
    {
      os << "(eo.SmtType ";
      osEnd << ")";
    }
    os << "tsm.Bool";
  }
  else
  {
    // Boolean constants are embedded as an SMT type, we have to wrap it
    // explicitly here.
    if (parent == MetaKind::EUNOIA)
    {
      os << "(eo.SmtTerm ";
      osEnd << ")";
    }
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
        os << "(sm.Bool ";
        osEnd << ")";
      }
      os << (l->d_bool ? "true" : "false");
    }
    else if (k == Kind::NUMERAL)
    {
      if (!isSmtBuiltin)
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
      if (!isSmtBuiltin)
      {
        os << "(sm.Rational ";
        osEnd << ")";
      }
      os << c;
    }
    else if (k == Kind::BINARY)
    {
      if (!isSmtBuiltin)
      {
        os << "(sm.Binary";
        osEnd << ")";
      }
      const BitVector& bv = l->d_bv;
      const Integer& bvi = bv.getValue();
      os << bv.getSize() << " " << bvi.toString();
    }
    else if (k == Kind::STRING)
    {
      if (!isSmtBuiltin)
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
}

bool SmtMetaReduce::printEmbPatternMatch(const Expr& c,
                                         const std::string& initCtx,
                                         std::ostream& os,
                                         SelectorCtx& ctx,
                                         ConjPrint& print,
                                         MetaKind tinit)
{
  tinit = tinit == MetaKind::NONE ? MetaKind::EUNOIA : tinit;
  // third tuple is a context which indicates the final SMT
  // type we are printing (eo.Term vs. sm.Term)
  std::map<Expr, std::string>::iterator it;
  std::vector<std::tuple<Expr, std::string, MetaKind>> visit;
  std::tuple<Expr, std::string, MetaKind> cur;
  visit.emplace_back(c, initCtx, tinit);
  do
  {
    cur = visit.back();
    visit.pop_back();
    Expr tcur = std::get<0>(cur);
    std::string currTerm = std::get<1>(cur);
    MetaKind parent = std::get<2>(cur);
    Kind ck = tcur.getKind();
    std::stringstream cname;
    bool printArgs = false;
    size_t printArgStart = 0;
    // std::cout << "  patMatch: " << tcur << " / " << currTerm << " / "
    //           << metaKindToString(parent) << " / kind " << ck
    //           << std::endl;
    // std::cout << "  atk: " << tcur << std::endl;
    MetaKind child = getMetaKindReturn(tcur, parent);
    // std::cout << "  atk: " << tcur << " is " << metaKindToString(atk)
    //           << std::endl;
    //  if the Eunoia term is an SMT term, change the context
    //  and use the eo.SmtTerm selector
    if (parent != child)
    {
      if (parent == MetaKind::EUNOIA
          && (child == MetaKind::SMT || child == MetaKind::SMT_TYPE
              || child == MetaKind::SMT_VALUE))
      {
        std::string cons = metaKindToCons(child);
        std::stringstream tester;
        tester << "((_ is eo." << cons << ") " << currTerm << ")";
        print.push(tester.str());
        std::stringstream sssn;
        sssn << "(eo." << cons << ".arg1 " << currTerm << ")";
        currTerm = sssn.str();
        // our context is now updated
        parent = child;
      }
      else
      {
        EO_FATAL() << "Unhandled context change " << metaKindToString(parent)
                   << " / " << metaKindToString(child) << " in " << tcur
                   << " within " << c;
      }
    }
    if (ck == Kind::APPLY)
    {
      if (isProgram(tcur[0]))
      {
        EO_FATAL() << "Cannot match on program " << tcur[0];
      }
      Assert(tcur.getNumChildren() == 2);
      // Determine if this is a Eunoia internal term, or an
      // SMT term eagerly here
      // Use the appropriate prefix
      cname << metaKindToPrefix(parent) << "Apply";
      printArgs = true;
    }
    else if (ck == Kind::FUNCTION_TYPE)
    {
      // TODO: can this occur?
      // maybe if reasoning about function as first class argument?
      cname << metaKindToPrefix(parent) << "FunType";
      printArgs = true;
    }
    else if (ck == Kind::APPLY_OPAQUE)
    {
      // will use a tester
      printEmbAtomicTerm(tcur[0], cname, MetaKind::NONE);
      printArgStart = 1;
      if (isSmtApplyApp(tcur))
      {
        Assert(tcur[1].getKind() == Kind::STRING);
        // e.g. ($smt_apply_0 "0") in a pattern.
        const Literal* l = tcur[1].getValue()->asLiteral();
        std::stringstream eq;
        eq << "(= " << currTerm << " " << l->d_str.toString() << ")";
        print.push(eq.str());
        continue;
      }
      printArgs = true;
      // we don't know the context of children, we compute per child below
      parent = MetaKind::NONE;
    }
    if (printArgs)
    {
      // argument must be an apply
      std::stringstream tester;
      tester << "((_ is " << cname.str() << ") " << currTerm << ")";
      print.push(tester.str());
      std::vector<MetaKind> targs = getMetaKindArgs(tcur, parent);
      for (size_t i = printArgStart, nchild = tcur.getNumChildren(); i < nchild;
           i++)
      {
        std::stringstream ssNext;
        ssNext << "(" << cname.str() << ".arg" << (i + 1 - printArgStart) << " "
               << currTerm << ")";
        // the next type is "reset"
        visit.emplace_back(tcur[i], ssNext.str(), targs[i]);
      }
    }
    else if (ck == Kind::PARAM)
    {
      it = ctx.d_ctx.find(tcur);
      if (it == ctx.d_ctx.end())
      {
        // find time seeing this parameter, it is bound to the selector chain
        ctx.d_ctx[tcur] = currTerm;
        ctx.d_tctx[tcur] = parent;
        // std::cout << "PAT-MATCH: " << currTerm
        //           << " was matched in term context "
        //           << metaKindToString(parent) << std::endl;
      }
      else
      {
        MetaKind prev = ctx.d_tctx[tcur];
        if (prev != parent)
        {
          Assert(false) << "Variable " << tcur << " matched in two contexts "
                        << metaKindToString(parent) << " and "
                        << metaKindToString(prev) << ", within " << c
                        << ", (= " << currTerm << " " << it->second << ")";
        }
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
      // note that we have to use the full printEmbTerm method
      std::stringstream atomTerm;
      printEmbAtomicTerm(tcur, atomTerm, parent);
      std::stringstream eq;
      eq << "(= " << currTerm << " " << atomTerm.str() << ")";
      print.push(eq.str());
    }
  } while (!visit.empty());
  return true;
}

std::string SmtMetaReduce::getName(const Expr& e)
{
  std::stringstream ss;
  if (e.getNumChildren() == 0)
  {
    ss << e;
  }
  return ss.str();
}

bool SmtMetaReduce::isEmbedCons(const Expr& e)
{
  std::string sname = getName(e);
  return (sname.compare(0, 5, "$smd_") == 0);
}

bool SmtMetaReduce::isSmtApplyApp(const Expr& oApp)
{
  if (oApp.getKind() != Kind::APPLY_OPAQUE || oApp.getNumChildren() <= 1
      || oApp[1].getKind() != Kind::STRING)
  {
    return false;
  }
  std::string sname = getName(oApp[0]);
  return (sname.compare(0, 11, "$smt_apply_") == 0
          || sname.compare(0, 10, "$smt_type_") == 0);
}

std::string SmtMetaReduce::getEmbedName(const Expr& oApp)
{
  Assert(oApp.getKind() == Kind::APPLY_OPAQUE);
  std::string aname = getName(oApp[0]);
  if (aname == "$smt_apply_=")
  {
    return "=";
  }
  if (!isSmtApplyApp(oApp))
  {
    EO_FATAL() << "Expected smt apply app when asking for embed name " << oApp;
  }
  const Literal* l = oApp[1].getValue()->asLiteral();
  return l->d_str.toString();
}

bool SmtMetaReduce::printEmbTerm(const Expr& body,
                                 std::ostream& os,
                                 const SelectorCtx& ctx,
                                 MetaKind tinit)
{
  std::map<Expr, std::string>::const_iterator it;
  std::map<Expr, MetaKind>::const_iterator ittc;
  std::map<std::pair<Expr, MetaKind>, size_t> cparen;
  std::map<std::pair<Expr, MetaKind>, size_t>::iterator itc;
  std::stringstream osEnd;
  std::vector<Expr> ll;
  // maps smt apply terms to the tuple that they actually are
  std::map<std::pair<Expr, MetaKind>, MetaKind>::iterator itt;
  Expr t = body;
  std::vector<std::pair<Expr, MetaKind>> visit;
  std::pair<Expr, MetaKind> cur;
  Expr recTerm;
  tinit = tinit == MetaKind::NONE ? MetaKind::EUNOIA : tinit;
  visit.emplace_back(t, tinit);
  do
  {
    cur = visit.back();
    recTerm = cur.first;
    // we use "null" for a space
    if (recTerm.isNull())
    {
      os << " ";
      visit.pop_back();
      continue;
    }
    MetaKind parent = cur.second;
    std::pair<Expr, MetaKind> key(recTerm, parent);
    itc = cparen.find(key);
    if (itc != cparen.end())
    {
      // NONE context means done with arguments, close the pending parens
      for (size_t i = 0; i < itc->second; i++)
      {
        os << ")";
      }
      visit.pop_back();
      cparen.erase(key);
      continue;
    }
    // otherwise, we check for a change of context and insert a cast if
    // necessary compute the child context
    Kind ck = recTerm.getKind();
    MetaKind child = MetaKind::NONE;
    if (ck == Kind::PARAM)
    {
      // If a parameter, it depends on the context in which it was matched,
      // which was stored as part of the selector context.
      // TODO: maybe it is just call getMetaKindReturn here??
      ittc = ctx.d_tctx.find(recTerm);
      // Assert(ittc != ctx.d_tctx.end()) << "Cannot find context " << recTerm;
      if (ittc != ctx.d_tctx.end())
      {
        child = ittc->second;
      }
    }
    else
    {
      child = getMetaKindReturn(recTerm, parent);
    }
    Assert(child != MetaKind::NONE)
        << "Failed to get child context for " << recTerm;
    // std::cout << "print: " << recTerm << " (" << ck << "), "
    //           << metaKindToString(parent) << " / "
    //           << metaKindToString(child) << std::endl;
    if (parent != MetaKind::NONE && parent != child)
    {
      if (parent == MetaKind::EUNOIA)
      {
        if (child == MetaKind::SMT || child == MetaKind::SMT_BUILTIN)
        {
          // going from a Eunoia term to an SMT term
          os << "(eo.SmtTerm ";
          cparen[key]++;
          // literals will be processed in printEmbAtomicTerm.
          parent = MetaKind::SMT;
        }
        else if (child == MetaKind::SMT_TYPE)
        {
          // going from a Eunoia term to an SMT type
          os << "(eo.SmtType ";
          cparen[key]++;
          parent = MetaKind::SMT_TYPE;
        }
      }
      if (child == MetaKind::EUNOIA)
      {
        // TODO: revisit this
        // A Eunoia term embedded in an SMT context. For
        // soundness, we must ensure that the Eunoia term has definitely
        // evaluated successfully. If so then we may use an SMT-LIB
        // selector that will have a total semantics.
        bool isTotal = false;
        if (recTerm.isGround() && !recTerm.isEvaluatable())
        {
          // The term is ground and has no occurrences of evaluatable
          // operators, we are clearly total.
          isTotal = true;
        }
        else if (ck == Kind::PARAM)
        {
          // If we are a parameter, then based on the conditions in
          // the preamble of the function, we have guarded against
          // stuckness and thus may assume totality here.
          isTotal = true;
        }
        if (isSmtLibExpression(parent) && isTotal)
        {
          os << "(eo." << metaKindToCons(parent) << ".arg1 ";
          cparen[key]++;
          // we now can consider the child to be an (unguarded) Eunoia term
          parent = MetaKind::EUNOIA;
        }
      }
      if (parent == MetaKind::SMT)
      {
        if (child == MetaKind::SMT_BUILTIN)
        {
          // wrap the literal types
          if (ck == Kind::NUMERAL)
          {
            os << "(sm.Numeral ";
            cparen[key]++;
          }
          else if (ck == Kind::RATIONAL)
          {
            os << "(sm.Rational ";
            cparen[key]++;
          }
          else if (ck == Kind::BINARY)
          {
            os << "(sm.Binary";
            cparen[key]++;
          }
          else if (ck == Kind::STRING)
          {
            os << "(sm.String ";
            cparen[key]++;
          }
          parent = MetaKind::SMT_BUILTIN;
        }
      }
#if 1
      Assert(parent == child)
          << "Unhandled context switch for " << recTerm << " "
          << recTerm.getKind() << std::endl
          << metaKindToString(parent) << " -> " << metaKindToString(child)
          << " within term " << body;
#endif
    }
    // We now should only care about the child context!!!

    // if we are printing the head of the term
    if (ck == Kind::PARAM)
    {
      // parameters print as the string that gives the term they were matched to
      it = ctx.d_ctx.find(recTerm);
      // Assert(it != ctx.d_ctx.end()) << "Cannot find " << recTerm;
      if (it != ctx.d_ctx.end())
      {
        os << it->second;
      }
      else
      {
        os << recTerm;
      }
      // dont pop back if we need to close parens
      if (cparen.find(key) == cparen.end())
      {
        visit.pop_back();
      }
      continue;
    }
    else if (recTerm.getNumChildren() == 0)
    {
      // atomic terms print here
      // We handle SMT vs SMT_BUILTIN within that method
      // std::cout << "print emb atomic term: " << recTerm << std::endl;
      printEmbAtomicTerm(recTerm, os);
      // dont pop back if we need to close parens
      if (cparen.find(key) == cparen.end())
      {
        visit.pop_back();
      }
      continue;
    }
    // we always push all children at once
    size_t cstart = 0;
    if (ck == Kind::APPLY)
    {
      os << "(";
      cparen[key]++;
      // programs print as themselves
      if (!isProgramApp(recTerm))
      {
        Assert(child == MetaKind::EUNOIA);
        // Note that we use eo.Apply unguarded. In particular, the
        // flatten-eval step has ensured that constructing Eunoia terms
        // in this way will not get stuck during term construction, but
        // instead of program invocation.
        os << "eo.Apply ";
      }
    }
    else if (ck == Kind::APPLY_OPAQUE)
    {
      std::stringstream ss;
      ss << recTerm[0];
      std::string sname = ss.str();
      // operators that print the identifier embedding e.g.
      // `($smt_apply_3 "ite"` becomes `(ite`
      if (sname.compare(0, 11, "$smt_apply_") == 0
          || sname.compare(0, 10, "$smt_type_") == 0)
      {
        std::string embName = getEmbedName(recTerm);
        if (embName == "=")
        {
          os << "(= ";
          cparen[key]++;
          cstart = 1;
        }
        else if (recTerm.getNumChildren() > 2)
        {
          os << "(" << embName << " ";
          cparen[key]++;
          cstart = 2;
        }
        else
        {
          // this handles the corner case that ($smt_apply_0 "true") should
          // print as "true" not "(true)".
          // Assert (!embName.empty()) << "empty embed name, from " << recTerm;
          os << embName;
          // don't pop as we may need to process closing parens if casted
          if (cparen.find(key) == cparen.end())
          {
            visit.pop_back();
          }
          continue;
        }
      }
      else
      {
        // all other operators print as applications
        os << "(";
        cparen[key]++;
      }
    }
    else if (ck == Kind::FUNCTION_TYPE)
    {
      Assert(recTerm.getNumChildren() == 2);
      // use the final deep embedding
      os << "(eo.FunType ";
      cparen[key]++;
    }
    else if (isLiteralOp(ck))
    {
      // ensure the remaining eo:: are eliminated
      std::string kstr = kindToTerm(ck);
      if (kstr.compare(0, 4, "eo::") == 0)
      {
        os << "($eo_" << kstr.substr(4) << " ";
        cparen[key]++;
      }
      else
      {
        EO_FATAL() << "Bad name for literal kind " << ck << std::endl;
      }
    }
    else
    {
      EO_FATAL() << "Unhandled kind in print term " << ck << " " << recTerm
                 << " / " << metaKindToString(parent) << std::endl;
    }
    // otherwise, the new context depends on the types of the children
    std::vector<MetaKind> targs = getMetaKindArgs(recTerm, parent);
    // push in reverse order
    size_t nchild = recTerm.getNumChildren();
    for (size_t i = cstart; i < nchild; i++)
    {
      if (i != cstart)
      {
        // add a space after the argument, unless the last (first) argument
        visit.emplace_back(d_null, MetaKind::NONE);
      }
      size_t ii = cstart + (nchild - i) - 1;
      Expr rc = recTerm[ii];
      MetaKind ctxRec = targs[ii];
      visit.emplace_back(rc, ctxRec);
    }
  } while (!visit.empty());
  return true;
}

void SmtMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  // have to wait, due to dependence on $eo_get_meta_type being defined.
  d_progSeen.emplace_back(v, prog);
}

void SmtMetaReduce::finalizePrograms()
{
  for (const std::pair<Expr, Expr>& p : d_progSeen)
  {
    finalizeProgram(p.first, p.second);
  }
}

void SmtMetaReduce::finalizeProgram(const Expr& v, const Expr& prog)
{
  std::string vname = getName(v);
  std::cout << "*** Setting up program " << v << " / " << !prog.isNull()
            << std::endl;
  d_defs << "; " << (prog.isNull() ? "fwd-decl: " : "program: ") << v
         << std::endl;
  std::stringstream decl;
  Expr vv = v;
  Expr vt = d_tc.getType(vv);
  std::vector<MetaKind> vctxArgs;
  size_t nargs = vt.getNumChildren();
  for (size_t j = 0; j < nargs; j++)
  {
    vctxArgs.push_back(getTypeMetaKind(vt[j]));
  }
  // std::cout << "Type is " << vt << std::endl;
  decl << "(declare-fun " << v << " (";
  std::stringstream varList;
  Assert(vt.getKind() == Kind::PROGRAM_TYPE)
      << "bad type " << vt << " for " << v;
  Assert(nargs > 1);
  std::vector<std::string> args;
  std::stringstream appTerm;
  appTerm << "(" << v;
  ConjPrint printStuck;
  for (size_t i = 1; i < nargs; i++)
  {
    if (i > 1)
    {
      decl << " ";
      varList << " ";
    }
    std::stringstream argType;
    printMetaType(vt[i - 1], argType, MetaKind::EUNOIA);
    decl << argType.str();
    std::stringstream ssArg;
    ssArg << "x" << i;
    appTerm << " " << ssArg.str();
    args.emplace_back(ssArg.str());
    varList << "(" << ssArg.str() << " " << argType.str() << ")";
    // don't have to check stuckness if type is not Eunoia
    if (vctxArgs[i - 1] == MetaKind::EUNOIA)
    {
      std::stringstream ssCurr;
      ssCurr << "(= " << ssArg.str() << " eo.Stuck)";
      printStuck.push(ssCurr.str());
    }
  }
  appTerm << ")";
  std::stringstream retType;
  printMetaType(vt[nargs - 1], retType, MetaKind::EUNOIA);
  decl << ") " << retType.str() << ")" << std::endl;
  // std::cout << "DECLARE " << decl.str() << std::endl;
  //  if forward declared, we are done for now
  if (prog.isNull())
  {
    d_progDeclProcessed.insert(v);
    d_defs << decl.str() << std::endl;
    return;
  }
  std::cout << "*** FINALIZE " << v << std::endl;
  bool reqAxiom = (d_progDeclProcessed.find(v) != d_progDeclProcessed.end());
  // compile the pattern matching
  std::stringstream cases;
  std::stringstream casesEnd;
  // start with stuck case, if not a SMT program
  // TODO: make more robust by looking at types???
  bool isSmtProgram = (vname.compare(0, 6, "$smtx_") == 0);
  bool isEoProg = !isSmtProgram;
  if (isEoProg)
  {
    cases << "  (ite ";
    printStuck.printConjunction(cases, true);
    cases << std::endl << "    eo.Stuck" << std::endl;
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
    ConjPrint print;
    Assert(hd.getNumChildren() == nargs);
    for (size_t j = 1, nhdchild = hd.getNumChildren(); j < nhdchild; j++)
    {
      // Print the pattern matching predicate for this argument, all
      // concatenated together.
      // Initial context depends on the kind of the argument type of the
      // program.
      MetaKind ctxPatMatch = vctxArgs[j - 1];
      std::cout << std::endl
                << "; Print pat matching for " << hd[j] << " in context "
                << metaKindToString(ctxPatMatch) << std::endl;
      printEmbPatternMatch(
          hd[j], args[j - 1], currCase, ctx, print, ctxPatMatch);
      std::cout << "...returns \"" << currCase.str() << "\"" << std::endl;
    }
    // compile the return for this case
    std::stringstream currRet;
    // The type of the function determines the initial context of return terms
    // we print
    MetaKind bodyInitCtx = vctxArgs[nargs - 1];
    std::cout << std::endl
              << "; Print body " << body << " in context "
              << metaKindToString(bodyInitCtx) << std::endl;
    printEmbTerm(body, currRet, ctx, bodyInitCtx);
    std::cout << "...returns \"" << currRet.str() << "\"" << std::endl;
    if (isEoProg || isSmtProgram)
    {
      // we permit SMT_PROGRAM and Eunoia programs to have pattern matching
      // now print the case/return
      // for SMT_PROGRAM, the last case is assumed to be total
      // this is part of the trusted core: to ensure all programs in
      // model_smt.eo are total.
      if (i + 1 < ncases || !isSmtProgram)
      {
        cases << "  (ite ";
        print.printConjunction(cases);
        cases << std::endl;
        casesEnd << ")";
      }
      cases << "    " << currRet.str() << std::endl;
    }
    else
    {
      if (i > 0 && !isSmtProgram)
      {
        EO_FATAL()
            << "Program " << v
            << " is not a Eunoia program and thus cannot have multiple cases";
      }
      if (print.d_npush > 0)
      {
        EO_FATAL() << "Program " << v
                   << " is not a Eunoia program and thus cannot rely on "
                      "pattern matching";
      }
      cases << "  " << currRet.str() << std::endl;
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

void SmtMetaReduce::finalize()
{
  finalizePrograms();

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

  replace(finalSm, "$SM_DEFS$", d_defs.str());
  replace(finalSm, "$SMT_VC$", d_smtVc.str());

  std::stringstream sso;
  sso << s_plugin_path << "plugins/smt_meta/smt_meta_gen.smt2";
  std::cout << "Write smt2-defs " << sso.str() << std::endl;
  std::ofstream out(sso.str());
  out << finalSm;
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
    std::stringstream eoTrue;
    eoTrue << "(eo.SmtTerm (sm.Bool true))";
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
        d_smtVc << "(x" << i << " eo.Term)";
        call << " x" << i;
      }
      d_smtVc << ")" << std::endl;
      d_smtVc << "  (= (" << eosc << call.str() << ") " << eoTrue.str() << "))";
    }
    else
    {
      d_smtVc << "(= " << eosc << " " << eoTrue.str() << "))";
    }
    d_smtVc << " :named sm.conjecture." << vv << ")";
    d_smtVc << ")" << std::endl;
    // std::cout << "...set target" << std::endl;
    return false;
  }
  return true;
}

bool SmtMetaReduce::isProgram(const Expr& t)
{
  return (t.getKind() == Kind::PROGRAM_CONST);
}

bool SmtMetaReduce::isSmtLibExpression(MetaKind ctx)
{
  return ctx == MetaKind::SMT || ctx == MetaKind::SMT_TYPE
         || ctx == MetaKind::SMT_VALUE;
}

MetaKind SmtMetaReduce::getTypeMetaKind(const Expr& typ, MetaKind elseKind)
{
  Kind k = typ.getKind();
  if (k == Kind::APPLY_OPAQUE)
  {
    std::string sname = getName(typ[0]);
    if (sname.compare(0, 10, "$smt_type_") == 0)
    {
      return MetaKind::SMT_BUILTIN;
    }
  }
  std::string sname = getName(typ);
  if (sname == "$eo_Term")
  {
    return MetaKind::EUNOIA;
  }
  else if (sname == "$smt_Term")
  {
    return MetaKind::SMT;
  }
  else if (sname == "$smt_Type")
  {
    return MetaKind::SMT_TYPE;
  }
  else if (sname == "$smt_Value")
  {
    return MetaKind::SMT_VALUE;
  }
  else if (sname == "$smt_Map")
  {
    return MetaKind::SMT_MAP;
  }
  else if (sname == "$smt_BuiltinType")
  {
    return MetaKind::SMT_BUILTIN;
  }
  return elseKind;
}

MetaKind SmtMetaReduce::getMetaKind(State& s, const Expr& e, std::string& cname)
{
  std::string sname = getName(e);
  // terms starting with @ are considered Eunoia (not SMT-LIB)
  if (sname.compare(0, 1, "@") == 0 || sname.compare(0, 8, "$eo_List") == 0)
  {
    cname = sname;
    return MetaKind::EUNOIA;
  }
  else if (sname.compare(0, 4, "$eo_") == 0
           || sname.compare(0, 5, "$smt_") == 0)
  {
    // internal-only symbol
    cname = sname;
    return MetaKind::SMT_BUILTIN;
  }
  else if (sname.compare(0, 5, "$smd_") == 0)
  {
    size_t firstDot = sname.find('.');
    std::string prefix = sname.substr(5, firstDot - 5);
    cname = sname.substr(firstDot + 1);
    return prefixToMetaKind(prefix);
  }
  cname = sname;
  // If not a distinguished symbol, it may be an SMT-LIB term or a type.
  // Check the type of e.
  Expr c = e;
  Expr tc = s.getTypeChecker().getType(c);
  if (tc.getKind() == Kind::TYPE
      || (tc.getKind() == Kind::FUNCTION_TYPE
          && tc[tc.getNumChildren() - 1].getKind() == Kind::TYPE))
  {
    return MetaKind::SMT_TYPE;
  }
  return MetaKind::SMT;
}

MetaKind SmtMetaReduce::getMetaKindArg(const Expr& parent,
                                       size_t i,
                                       MetaKind parentCtx)
{
  // This method should rely on the parent only!!!
  MetaKind tk = MetaKind::NONE;
  Kind k = parent.getKind();
  if (k == Kind::APPLY_OPAQUE)
  {
    // the head of the opaque is NONE
    if (i == 0)
    {
      return tk;
    }
    std::string sname = getName(parent[0]);
    MetaKind tknew;
    if (sname.compare(0, 5, "$smd_") == 0)
    {
      // any operator introduced by $smd_ should have accurate type.
      Expr op = parent[0];
      Expr tpop = d_tc.getType(op);
      Assert(tpop.getKind() == Kind::FUNCTION_TYPE)
          << "Not function " << parent;
      std::pair<std::vector<Expr>, Expr> ftype = tpop.getFunctionType();
      Assert(i <= ftype.first.size())
          << "Bad index " << (i - 1) << " / " << tpop << " from " << parent;
      std::cout << "Get type meta kind for " << ftype.first[i - 1] << std::endl;
      Expr atype = ftype.first[i - 1];
      if (atype.getKind() == Kind::QUOTE_TYPE)
      {
        Expr qt = atype[0];
        atype = d_tc.getType(qt);
      }
      std::cout << "...process to " << atype << std::endl;
      tknew = getTypeMetaKind(atype);
      Assert(tknew != MetaKind::NONE);
      return tknew;
    }
    if (sname.compare(0, 11, "$smt_apply_") == 0)
    {
      std::string suffix = sname.substr(11);
      if (suffix == "=")
      {
        // both sides have no context.
        // this allows SMT-LIB equality to operate on Eunoia terms.
        tk = MetaKind::NONE;
      }
      else if (i == 1)
      {
        // SMT-LIB identifier
        tk = MetaKind::NONE;
      }
      else
      {
        std::string esname = getEmbedName(parent);
        if (esname == "ite")
        {
          // the condition is stored at position 2, after op and deep
          // embedding the branches have no context.
          // TODO: maybe they should have SMT context???
          tk = i == 2 ? MetaKind::SMT_BUILTIN : MetaKind::NONE;
        }
        else if (esname.compare(0, 6, "(_ is ") == 0)
        {
          size_t firstDot = esname.find('.');
          Assert(firstDot != std::string::npos && firstDot > 6);
          std::string prefix = esname.substr(6, firstDot - 6);
          tk = prefixToMetaKind(prefix);
        }
        else
        {
          Assert(esname != "=") << "Use smt_apply_= instead";
          tk = MetaKind::SMT_BUILTIN;
        }
      }
    }
    else if (sname.compare(0, 10, "$smt_type_") == 0)
    {
      tk = MetaKind::SMT_TYPE;
    }
  }
  else if (k == Kind::APPLY)
  {
    if (isProgramApp(parent))
    {
      if (i == 0)
      {
        // the program head has no context
        return MetaKind::NONE;
      }
      // if program app, depends on the type of the program
      Expr p = parent[0];
      Expr ptype = d_tc.getType(p);
      Assert(ptype.getKind() == Kind::PROGRAM_TYPE);
      // convert the type to a metakind
      Assert(i < ptype.getNumChildren())
          << "Asking for child " << i << " of " << parent
          << ", not enough types " << ptype;
      // assume Eunoia if the type is not one of the expected corner cases
      tk = getTypeMetaKind(ptype[i - 1]);
    }
    else
    {
      // the application case depends on the meta-kind of the head term
      tk = getMetaKindReturn(parent, parentCtx);
    }
  }
  else if (k == Kind::FUNCTION_TYPE)
  {
    tk = MetaKind::EUNOIA;
  }
  else if (isLiteralOp(k))
  {
    // all remaining builtins assume Eunoia arguments
    tk = MetaKind::EUNOIA;
  }
  else
  {
    Assert(false) << "Unknown apply term kind for getMetaKindArg: " << k;
  }
  return tk;
}

bool SmtMetaReduce::isProgramApp(const Expr& app)
{
  return (app.getKind() == Kind::APPLY
          && app[0].getKind() == Kind::PROGRAM_CONST);
}

MetaKind SmtMetaReduce::getMetaKindReturn(const Expr& child, MetaKind parentCtx)
{
  Assert(!child.isNull()) << "null term for meta kind";
  MetaKind tk = MetaKind::NONE;
  Expr hd = child;
  Kind k = hd.getKind();
  if (hd.getKind() == Kind::APPLY)
  {
    // check for programs
    if (isProgramApp(hd))
    {
      // if program app, depends on the type of the program
      Expr p = hd[0];
      Expr ptype = d_tc.getType(p);
      Assert(ptype.getKind() == Kind::PROGRAM_TYPE);
      // convert the type to a metakind
      return getTypeMetaKind(ptype[ptype.getNumChildren() - 1]);
    }
    // all other apply is Eunoia
    return MetaKind::EUNOIA;
  }
  else if (k == Kind::APPLY_OPAQUE)
  {
    std::string sname = getName(child[0]);
    if (sname.compare(0, 11, "$smt_apply_") == 0)
    {
      std::string suffix = sname.substr(11);
      if (suffix == "=")
      {
        // builtin equality returns an SMT-LIB builtin
        tk = MetaKind::SMT_BUILTIN;
      }
      else
      {
        std::string esname = getEmbedName(child);
        if (esname == "ite")
        {
          Assert(child.getNumChildren() == 5);
          tk = getMetaKindReturn(child[3], parentCtx);
          MetaKind k2 = getMetaKindReturn(child[4], parentCtx);
          Assert(tk == k2) << "ITE branches have different meta types " << child
                           << " " << metaKindToString(tk) << " and "
                           << metaKindToString(k2);
        }
        else if (esname == "=")
        {
          MetaKind k1 = getMetaKindReturn(child[2], parentCtx);
          MetaKind k2 = getMetaKindReturn(child[3], parentCtx);
          Assert(k1 == k2) << "Equal sides have different meta types " << child
                           << " " << metaKindToString(k1) << " "
                           << metaKindToString(k2);
          tk = MetaKind::SMT_BUILTIN;
        }
        else
        {
          tk = MetaKind::SMT_BUILTIN;
        }
      }
    }
    else if (sname.compare(0, 10, "$smt_type_") == 0)
    {
      tk = MetaKind::SMT_TYPE;
    }
    else if (sname.compare(0, 5, "$smd_") == 0)
    {
      Expr op = child[0];
      Expr tpop = d_tc.getType(op);
      std::pair<std::vector<Expr>, Expr> ftype = tpop.getFunctionType();
      MetaKind tknew = getTypeMetaKind(ftype.second);
      Assert(tknew != MetaKind::NONE);
      return tknew;
    }
    else if (sname == "$eo_Var")
    {
      tk = MetaKind::EUNOIA;
    }
    else
    {
      Assert(false) << "Unknown opaque app " << sname
                    << " in get meta kind return " << child;
    }
  }
  else if (k == Kind::BOOL_TYPE)
  {
    // the Bool type is Eunoia Bool. use ($smt.type_0 "Bool") for builtin
    // SMT-LIB Bool
    tk = MetaKind::EUNOIA;
  }
  else if (isLiteral(k))
  {
    // TODO: is this right?? whereas Boolean is implicitly SMT?
    tk = MetaKind::EUNOIA;
  }
  else if (k == Kind::PROGRAM_CONST)
  {
    tk = MetaKind::PROGRAM;
  }
  else if (k == Kind::FUNCTION_TYPE || k == Kind::TYPE)
  {
    // for now, function type is assumed to be Eunoia.
    // likely HO smt would change this.
    tk = MetaKind::EUNOIA;
  }
  else if (isLiteralOp(k))
  {
    tk = MetaKind::EUNOIA;
  }
  else if (hd.getNumChildren() == 0)
  {
    std::string sname = getName(hd);
    Expr htype = d_tc.getType(hd);
    Assert(!htype.isNull()) << "Failed to type check " << hd;
    // Nullary deep embedding constructors
    if (sname.compare(0, 5, "$smd_") == 0)
    {
      MetaKind tknew = getTypeMetaKind(htype);
      Assert(tknew != MetaKind::NONE);
      return tknew;
    }
    tk = getTypeMetaKind(htype);
    // std::cout << "Type for atomic term " << hd << " (" << k << ") is "
    //           << htype << ", thus context is " <<
    //           metaKindToString(tk)
    //           << std::endl;
    // if it is a Eunoia constant, it depends on the naming
    // convention
    if (k == Kind::CONST && tk == MetaKind::EUNOIA)
    {
      // otherwise, use the meta kind utility.
      std::string cnameTmp;
      tk = getMetaKind(d_state, hd, cnameTmp);
      if (tk == MetaKind::NONE && parentCtx != MetaKind::NONE)
      {
        // otherwise just use the parent type????
        tk = parentCtx;
      }
      // std::cout << "...evaluate meta-kind side condition returns " << mm
      //           << ", which is " << metaKindToString(tk) <<
      //           std::endl;
    }
    else if (parentCtx != MetaKind::NONE)
    {
      // otherwise trust the parent kind???
      tk = parentCtx;
    }
  }
  else
  {
    Assert(false) << "Unknown apply term kind for getMetaKindReturn: " << k;
  }
  return tk;
}

std::vector<MetaKind> SmtMetaReduce::getMetaKindArgs(const Expr& parent,
                                                     MetaKind parentCtx)
{
  std::vector<MetaKind> args;
  std::cout << "  MetaArg: " << parent << " / " << metaKindToString(parentCtx)
            << std::endl;
  for (size_t i = 0, nchild = parent.getNumChildren(); i < nchild; i++)
  {
    MetaKind ctx = getMetaKindArg(parent, i, parentCtx);
    std::cout << "    MetaArgChild: " << metaKindToString(ctx) << " for "
              << parent[i] << std::endl;
    args.push_back(ctx);
  }
  std::cout << "  MetaArg: end" << std::endl;
  return args;
}

}  // namespace ethos
