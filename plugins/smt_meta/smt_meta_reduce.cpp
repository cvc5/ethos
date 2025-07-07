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

std::string termContextKindToString(TermContextKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case TermContextKind::EUNOIA: ss << "EUNOIA"; break;
    case TermContextKind::SMT: ss << "SMT"; break;
    case TermContextKind::SMT_BUILTIN: ss << "SMT_BUILTIN"; break;
    case TermContextKind::SMT_TYPE: ss << "SMT_TYPE"; break;
    case TermContextKind::SMT_GUARDED: ss << "SMT_GUARDED"; break;
    case TermContextKind::SMT_TYPE_GUARDED: ss << "SMT_TYPE_GUARDED"; break;
    case TermContextKind::SMT_VALUE_GUARDED: ss << "SMT_VALUE_GUARDED"; break;
    case TermContextKind::SMT_VALUE: ss << "SMT_VALUE"; break;
    case TermContextKind::SMT_MAP: ss << "SMT_MAP"; break;
    case TermContextKind::PROGRAM: ss << "PROGRAM"; break;
    case TermContextKind::NONE: ss << "NONE"; break;
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
    case TermContextKind::SMT:
    case TermContextKind::SMT_GUARDED: ss << "sm."; break;
    case TermContextKind::SMT_TYPE:
    case TermContextKind::SMT_TYPE_GUARDED: ss << "tsm."; break;
    case TermContextKind::SMT_VALUE:
    case TermContextKind::SMT_VALUE_GUARDED: ss << "vsm."; break;
    case TermContextKind::SMT_BUILTIN: ss << "?"; break;
    default:
      ss << "?TermContextKindPrefix_" << termContextKindToString(k);
      break;
  }
  return ss.str();
}
std::string termContextKindToCons(TermContextKind k)
{
  std::stringstream ss;
  switch (k)
  {
    case TermContextKind::SMT:
    case TermContextKind::SMT_GUARDED: ss << "SmtTerm"; break;
    case TermContextKind::SMT_TYPE:
    case TermContextKind::SMT_TYPE_GUARDED: ss << "SmtType"; break;
    case TermContextKind::SMT_VALUE:
    case TermContextKind::SMT_VALUE_GUARDED: ss << "SmtValue"; break;
    default: ss << "?TermContextKindCons"; break;
  }
  return ss.str();
}

void SmtMetaReduce::bind(const std::string& name, const Expr& e)
{
  // NOTE: the code here ensures that (if needed) we can preserve
  // definitions for the final vc, if it is necessary for debugging.
  // Currently however these definitions are already inlined by the
  // Ethos parser. We would need a --preserve-defs option to Ethos
  // to allow this form of debugging.
  if (name.compare(0, 4, "$eo_") == 0 && e.getKind() == Kind::LAMBDA)
  {
    Expr p = e;
    // dummy type
    std::vector<Expr> argTypes;
    Assert(e[0].getKind() == Kind::TUPLE);
    Assert(e[0].getNumChildren() != 0);
    for (size_t i = 0, nargs = e[0].getNumChildren(); i < nargs; i++)
    {
      Expr aa = e[0][i];
      argTypes.push_back(d_tc.getType(aa));
    }
    Expr body = e[1];
    Expr retType = d_tc.getType(body);
    std::cout << "Look at define " << name << std::endl;
    Assert(!retType.isNull()) << "Cannot type check " << body;
    Expr pt = d_state.mkProgramType(argTypes, retType);
    std::cout << "....make program " << name << " for define, prog type is "
              << pt << std::endl;
    // Expr pt = d_state.mkBuiltinType(Kind::LAMBDA);
    Expr tmp = d_state.mkSymbol(Kind::PROGRAM_CONST, name, pt);
    d_progSeen.emplace_back(tmp, p);
    return;
  }
}

void SmtMetaReduce::printEmbAtomicTerm(const Expr& c,
                                       std::ostream& os,
                                       TermContextKind parent)
{
  parent = parent == TermContextKind::NONE ? TermContextKind::EUNOIA : parent;
  Kind k = c.getKind();
  if (k == Kind::TYPE)
  {
    os << "eo.Type";
    return;
  }
  std::string name;
  TermContextKind child = getMetaKindReturn(c, parent);
  if (child == TermContextKind::PROGRAM)
  {
    // programs always print verbatim
    os << c;
    return;
  }
  bool isSmtBuiltin = (parent == TermContextKind::SMT_BUILTIN);
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
      os << termContextKindToPrefix(child) << cname;
    }
  }
  else if (k == Kind::BOOL_TYPE)
  {
    // Bool is embedded as an SMT type, we have to wrap it explicitly here.
    if (parent == TermContextKind::EUNOIA)
    {
      os << "(eo.SmtType ";
      osEnd << ")";
    }
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
      // Boolean constants are embedded as an SMT type, we have to wrap it
      // explicitly here.
      if (parent == TermContextKind::EUNOIA)
      {
        os << "(eo.SmtTerm ";
        osEnd << ")";
      }
      if (!isSmtBuiltin)
      {
        os << "sm.";
        os << (l->d_bool ? "True" : "False");
      }
      else
      {
        os << (l->d_bool ? "true" : "false");
      }
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

void SmtMetaReduce::printEmbType(const Expr& c,
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
  Kind k = c.getKind();
  // if it is a reference to the deep embedding datatype,
  // then we print it.
  TermContextKind tk = getTypeMetaKind(c, TermContextKind::NONE);
  if (tk != TermContextKind::NONE)
  {
    switch (tk)
    {
      case TermContextKind::EUNOIA: os << "eo.Term"; break;
      case TermContextKind::SMT: os << "sm.Term"; break;
      case TermContextKind::SMT_TYPE: os << "tsm.Type"; break;
      case TermContextKind::SMT_VALUE: os << "vsm.Value"; break;
      case TermContextKind::SMT_BUILTIN: os << getEmbedName(c); break;
      default: break;
    }
    return;
  }
  if (k == Kind::PARAM || k == Kind::TYPE || k == Kind::BOOL_TYPE)
  {
    // Bool refers to (eo.SmtType tsm.Bool), which is a Eunoia term
    os << "eo.Term";
  }
  else if (k == Kind::APPLY)
  {
    // types print the same as terms
    SelectorCtx ctxNull;
    printEmbTerm(c, os, ctxNull, TermContextKind::SMT_TYPE);
  }
  else
  {
    std::string sname = getName(c);
    if (sname.compare(0, 8, "$eo_List") == 0)
    {
      os << "eo.Term";
    }
    else
    {
      Assert(false) << "Unknown type: " << c << " " << c.getKind();
    }
  }
  // else if (c == d_metaSmtValue)
  //{
  //  os << "sm.Type";
  //}
}

bool SmtMetaReduce::printEmbPatternMatch(const Expr& c,
                                         const std::string& initCtx,
                                         std::ostream& os,
                                         SelectorCtx& ctx,
                                         ConjPrint& print,
                                         TermContextKind tinit)
{
  tinit = tinit == TermContextKind::NONE ? TermContextKind::EUNOIA : tinit;
  // third tuple is a context which indicates the final SMT
  // type we are printing (eo.Term vs. sm.Term)
  std::map<Expr, std::string>::iterator it;
  std::vector<std::tuple<Expr, std::string, TermContextKind>> visit;
  std::tuple<Expr, std::string, TermContextKind> cur;
  visit.emplace_back(c, initCtx, tinit);
  do
  {
    cur = visit.back();
    visit.pop_back();
    Expr tcur = std::get<0>(cur);
    std::string currTerm = std::get<1>(cur);
    TermContextKind parent = std::get<2>(cur);
    Kind ck = tcur.getKind();
    std::stringstream cname;
    bool printArgs = false;
    size_t printArgStart = 0;
    // std::cout << "  patMatch: " << tcur << " / " << currTerm << " / "
    //           << termContextKindToString(parent) << " / kind " << ck
    //           << std::endl;
    // std::cout << "  atk: " << tcur << std::endl;
    TermContextKind atk = getMetaKindReturn(tcur, parent);
    // std::cout << "  atk: " << tcur << " is " << termContextKindToString(atk)
    //           << std::endl;
    //  if the Eunoia term is an SMT term, change the context
    //  and use the eo.SmtTerm selector
    if (parent != atk)
    {
      std::vector<TermContextKind> ctxChange;
      // NOTE: could do this, but it is making the Eunoia code too permissive???
      /*
      if (atk==TermContextKind::SMT_BUILTIN)
      {
        if (parent!=TermContextKind::SMT)
        {
          ctxChange.push_back(TermContextKind::SMT);
        }
      }
      */
      ctxChange.push_back(atk);
      for (size_t i = 0, nchange = ctxChange.size(); i < nchange; i++)
      {
        TermContextKind next = ctxChange[i];
        if (parent == TermContextKind::EUNOIA
            && (next == TermContextKind::SMT
                || next == TermContextKind::SMT_TYPE
                || next == TermContextKind::SMT_VALUE))
        {
          std::string cons = termContextKindToCons(next);
          std::stringstream tester;
          tester << "((_ is eo." << cons << ") " << currTerm << ")";
          print.push(tester.str());
          std::stringstream sssn;
          sssn << "(eo." << cons << ".arg1 " << currTerm << ")";
          currTerm = sssn.str();
          // our context is now updated
          parent = next;
        }
        else
        {
          EO_FATAL() << "Unhandled context change "
                     << termContextKindToString(parent) << " / "
                     << termContextKindToString(next) << " in " << tcur
                     << " within " << c;
        }
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
      cname << termContextKindToPrefix(parent) << "Apply";
      printArgs = true;
    }
    else if (ck == Kind::FUNCTION_TYPE)
    {
      // TODO: can this occur?
      // maybe if reasoning about function as first class argument?
      cname << termContextKindToPrefix(parent) << "FunType";
      printArgs = true;
    }
    else if (ck == Kind::APPLY_OPAQUE)
    {
      // will use a tester
      printEmbAtomicTerm(tcur[0], cname, TermContextKind::NONE);
      printArgStart = 1;
      printArgs = true;
      // we don't know the context of children, we compute per child below
      parent = TermContextKind::NONE;
    }
    if (printArgs)
    {
      // argument must be an apply
      std::stringstream tester;
      tester << "((_ is " << cname.str() << ") " << currTerm << ")";
      print.push(tester.str());
      std::vector<TermContextKind> targs = getMetaKindArgs(tcur, parent);
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
        //           << termContextKindToString(parent) << std::endl;
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
std::string SmtMetaReduce::getEmbedName(const Expr& oApp)
{
  Assert(oApp.getKind() == Kind::APPLY_OPAQUE);
  std::string aname = getName(oApp[0]);
  if (aname == "$smt_apply_=")
  {
    return "=";
  }
  if (oApp.getNumChildren() <= 1)
  {
    EO_FATAL() << "Unexpected arity for opaque operator " << oApp;
  }
  if (oApp[1].getKind() != Kind::STRING)
  {
    EO_FATAL() << "Expected string for SMT-LIB app name as first argument, got "
               << oApp;
  }
  const Literal* l = oApp[1].getValue()->asLiteral();
  return l->d_str.toString();
}

bool SmtMetaReduce::printEmbTerm(const Expr& body,
                                 std::ostream& os,
                                 const SelectorCtx& ctx,
                                 TermContextKind tinit)
{
  std::map<Expr, std::string>::const_iterator it;
  std::map<Expr, TermContextKind>::const_iterator ittc;
  std::map<std::pair<Expr, TermContextKind>, size_t> cparen;
  std::map<std::pair<Expr, TermContextKind>, size_t>::iterator itc;
  std::stringstream osEnd;
  std::vector<Expr> ll;
  // maps smt apply terms to the tuple that they actually are
  std::map<std::pair<Expr, TermContextKind>, TermContextKind>::iterator itt;
  Expr t = body;
  std::vector<std::pair<Expr, TermContextKind>> visit;
  std::pair<Expr, TermContextKind> cur;
  Expr recTerm;
  tinit = tinit == TermContextKind::NONE ? TermContextKind::EUNOIA : tinit;
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
    TermContextKind parent = cur.second;
    std::pair<Expr, TermContextKind> key(recTerm, parent);
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
    std::vector<Expr> rtermArgs;
    TermContextKind child;
    if (ck == Kind::PARAM)
    {
      // If a parameter, it depends on the context in which it was matched,
      // which was stored as part of the selector context.
      // TODO: maybe it is just call getMetaKindReturn here??
      ittc = ctx.d_tctx.find(recTerm);
      Assert(ittc != ctx.d_tctx.end()) << "Cannot find context " << recTerm;
      child = ittc->second;
    }
    else
    {
      child = getMetaKindReturn(recTerm, rtermArgs, parent);
    }
    Assert(child != TermContextKind::NONE)
        << "Failed to get child context for " << recTerm;
    // std::cout << "print: " << recTerm << " (" << ck << "), "
    //           << termContextKindToString(parent) << " / "
    //           << termContextKindToString(child) << std::endl;
    if (parent != TermContextKind::NONE && parent != child)
    {
      if (parent == TermContextKind::EUNOIA)
      {
        if (child == TermContextKind::SMT
            || child == TermContextKind::SMT_BUILTIN)
        {
          // going from a Eunoia term to an SMT term
          os << "(eo.SmtTerm ";
          cparen[key]++;
          // literals will be processed in printEmbAtomicTerm.
          parent = TermContextKind::SMT;
        }
        else if (child == TermContextKind::SMT_TYPE)
        {
          // going from a Eunoia term to an SMT type
          os << "(eo.SmtType ";
          cparen[key]++;
          parent = TermContextKind::SMT_TYPE;
        }
      }
      if (child == TermContextKind::EUNOIA)
      {
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
        else if (isGuardedArgSmtExpression(parent))
        {
          // We are using a datatype selector to extract and SMT-LIB
          // expression from a Eunoia term. Moreover, we are using
          // the selector in a way that is guarded.
          // isTotal = true;
        }
        if (isSmtLibExpression(parent) && isTotal)
        {
          os << "(eo." << termContextKindToCons(parent) << ".arg1 ";
          cparen[key]++;
          // we now can consider the child to be an (unguarded) Eunoia term
          parent = TermContextKind::EUNOIA;
        }
      }
      if (parent == TermContextKind::SMT
          || parent == TermContextKind::SMT_GUARDED)
      {
        if (child == TermContextKind::SMT_BUILTIN)
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
          parent = TermContextKind::SMT_BUILTIN;
        }
      }
#if 0
      Assert(parent == child)
          << "Unhandled context switch for " << recTerm << " "
          << recTerm.getKind() << std::endl
          << termContextKindToString(parent) << " -> "
          << termContextKindToString(child) << " within term " << body;
#endif
    }
    // We now should only care about the child context!!!

    // if we are printing the head of the term
    if (ck == Kind::PARAM)
    {
      // parameters print as the string that gives the term they were matched to
      it = ctx.d_ctx.find(recTerm);
      Assert(it != ctx.d_ctx.end()) << "Cannot find " << recTerm;
      os << it->second;
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
    // TODO: uncurry SMT-LIB apply terms
    // we always push all children at once
    size_t cstart = 0;
    bool isCurriedApply = false;
    if (ck == Kind::APPLY)
    {
      os << "(";
      cparen[key]++;
      // programs print as themselves
      if (!isProgramApp(recTerm))
      {
        isCurriedApply = true;
        if (child == TermContextKind::EUNOIA)
        {
          // use macro to ensure "Stuck" propagates
          os << "$eo_apply ";
        }
        else if (child == TermContextKind::SMT)
        {
          os << "sm.Apply ";
        }
        else if (child == TermContextKind::SMT_TYPE)
        {
          os << "tsm.Apply ";
        }
        else
        {
          Assert(false) << "Unhandled apply kind for " << recTerm << " "
                        << ", in context " << termContextKindToString(parent)
                        << " / " << termContextKindToString(child)
                        << " within term " << body;
        }
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
      // must use macro to ensure "Stuck" propagates
      os << "($eo_fun_type ";
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
                 << " / " << termContextKindToString(parent) << std::endl;
    }
    // FIXME: assume not, for now.
    isCurriedApply = false;
    // otherwise, the new context depends on the types of the children
    std::vector<TermContextKind> targs = getMetaKindArgs(recTerm, parent);
    // push in reverse order
    size_t nchild =
        (isCurriedApply ? rtermArgs.size() : recTerm.getNumChildren());
    for (size_t i = cstart; i < nchild; i++)
    {
      if (i != cstart)
      {
        // add a space after the argument, unless the last (first) argument
        visit.emplace_back(d_null, TermContextKind::NONE);
      }
      size_t ii = cstart + (nchild - i) - 1;
      Expr rc = (isCurriedApply ? rtermArgs[ii] : recTerm[ii]);
      TermContextKind ctxRec = (isCurriedApply ? child : targs[ii]);
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
    // This is only necessary if we want to preserve definitions
    // in the final VC (see ::bind).
    // We reduce defines to a program e.g.
    // (define foo ((x T)) (bar x))
    //   becomes
    // (program foo ((x T))
    //   :signature (T) (eo::typeof (bar x))
    //   (
    //   ((foo x) (bar x))
    //   )
    // )
    if (p.second.getKind() == Kind::LAMBDA)
    {
      Expr e = p.second;
      Assert(e[0].getKind() == Kind::TUPLE);
      std::vector<Expr> appChildren;
      appChildren.push_back(p.first);
      for (size_t i = 0, nargs = e[0].getNumChildren(); i < nargs; i++)
      {
        appChildren.push_back(e[0][i]);
      }
      Expr progApp = d_state.mkExprSimple(Kind::APPLY, appChildren);
      Expr pcase = d_state.mkPair(progApp, e[1]);
      Expr prog = d_state.mkExprSimple(Kind::PROGRAM, {pcase});
      std::cout << "...do program " << p.first << " / " << prog << " instead"
                << std::endl;
      finalizeProgram(p.first, prog);
      std::cout << "...finished lambda program" << std::endl;
      continue;
    }
    finalizeProgram(p.first, p.second);
  }
}

void SmtMetaReduce::finalizeProgram(const Expr& v, const Expr& prog)
{
  std::string vname = getName(v);
  // ignore programs used for defining this compilation itself
  // TODO: can remove if we are better at trim-def
  if (vname == "$eo_get_meta_type")
  {
    return;
  }
  d_defs << "; " << (prog.isNull() ? "fwd-decl: " : "program: ") << v
         << std::endl;
  std::stringstream decl;
  Expr vv = v;
  Expr vt = d_tc.getType(vv);
  std::vector<TermContextKind> vctxArgs;
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
    printEmbType(vt[i - 1], argType);
    decl << argType.str();
    std::stringstream ssArg;
    ssArg << "x" << i;
    appTerm << " " << ssArg.str();
    args.emplace_back(ssArg.str());
    varList << "(" << ssArg.str() << " " << argType.str() << ")";
    // don't have to check stuckness if type is not Eunoia
    if (vctxArgs[i - 1] == TermContextKind::EUNOIA)
    {
      std::stringstream ssCurr;
      ssCurr << "(= " << ssArg.str() << " eo.Stuck)";
      printStuck.push(ssCurr.str());
    }
  }
  appTerm << ")";
  std::stringstream retType;
  printEmbType(vt[nargs - 1], retType);
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
      TermContextKind ctxPatMatch = vctxArgs[j - 1];
       std::cout << std::endl
                 << "; Print pat matching for " << hd[j] << " in context "
                 << termContextKindToString(ctxPatMatch) << std::endl;
      printEmbPatternMatch(
          hd[j], args[j - 1], currCase, ctx, print, ctxPatMatch);
       std::cout << "...returns " << currCase.str() << std::endl;
    }
    // compile the return for this case
    std::stringstream currRet;
    // The type of the function determines the initial context of return terms
    // we print
    TermContextKind bodyInitCtx = vctxArgs[nargs - 1];
     std::cout << std::endl
               << "; Print body " << body << " in context "
               << termContextKindToString(bodyInitCtx) << std::endl;
    printEmbTerm(body, currRet, ctx, bodyInitCtx);
     std::cout << "...returns " << currRet.str() << std::endl;
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
  // Here, we expect $eo_get_meta_type to be defined as a function in the
  // signature, which is an oracle for saying which datatype a term belongs
  // to in the deep embedding. We expect this program to be defined as well
  // as the names of the types.
  d_eoGetMetaKind = lookupVar("$eo_get_meta_type");
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

bool SmtMetaReduce::isProgram(const Expr& t)
{
  return (t.getKind() == Kind::PROGRAM_CONST);
}

bool SmtMetaReduce::isSmtLibExpression(TermContextKind ctx)
{
  return ctx == TermContextKind::SMT || ctx == TermContextKind::SMT_TYPE
         || ctx == TermContextKind::SMT_VALUE || isGuardedArgSmtExpression(ctx);
}

bool SmtMetaReduce::isGuardedArgSmtExpression(TermContextKind ctx)
{
  return ctx == TermContextKind::SMT_GUARDED
         || ctx == TermContextKind::SMT_TYPE_GUARDED
         || ctx == TermContextKind::SMT_VALUE_GUARDED;
}

TermContextKind SmtMetaReduce::guard(TermContextKind ctx)
{
  switch (ctx)
  {
    case TermContextKind::SMT: return TermContextKind::SMT_GUARDED;
    case TermContextKind::SMT_TYPE: return TermContextKind::SMT_TYPE_GUARDED;
    case TermContextKind::SMT_VALUE: return TermContextKind::SMT_VALUE_GUARDED;
    default: break;
  }
  return ctx;
}

TermContextKind SmtMetaReduce::unguard(TermContextKind ctx)
{
  switch (ctx)
  {
    case TermContextKind::SMT_GUARDED: return TermContextKind::SMT;
    case TermContextKind::SMT_TYPE_GUARDED: return TermContextKind::SMT_TYPE;
    case TermContextKind::SMT_VALUE_GUARDED: return TermContextKind::SMT_VALUE;
    default: break;
  }
  return ctx;
}

TermContextKind SmtMetaReduce::getTypeMetaKind(const Expr& typ,
                                               TermContextKind elseKind)
{
  Kind k = typ.getKind();
  if (k == Kind::APPLY_OPAQUE)
  {
    std::string sname = getName(typ[0]);
    if (sname.compare(0, 10, "$smt_type_") == 0)
    {
      return TermContextKind::SMT_BUILTIN;
    }
  }
  std::string sname = getName(typ);
  if (sname == "$eo_Term")
  {
    return TermContextKind::EUNOIA;
  }
  else if (sname == "$smt_Term")
  {
    return TermContextKind::SMT;
  }
  else if (sname == "$smt_Type")
  {
    return TermContextKind::SMT_TYPE;
  }
  else if (sname == "$smt_Value")
  {
    return TermContextKind::SMT_VALUE;
  }
  return elseKind;
}

TermContextKind SmtMetaReduce::getMetaKindArg(const Expr& parent,
                                              size_t i,
                                              TermContextKind parentCtx)
{
  // This method should rely on the parent only!!!
  TermContextKind tk = TermContextKind::NONE;
  Kind k = parent.getKind();
  if (k == Kind::APPLY_OPAQUE)
  {
    // the head of the opaque is NONE
    if (i != 0)
    {
      std::string sname = getName(parent[0]);
      if (sname.compare(0, 11, "$smt_apply_") == 0)
      {
        std::string suffix = sname.substr(11);
        if (suffix == "=")
        {
          // both sides have no context.
          // this allows SMT-LIB equality to operate on Eunoia terms.
          tk = TermContextKind::NONE;
        }
        else if (i == 1)
        {
          // SMT-LIB identifier, ignore
          tk = TermContextKind::NONE;
        }
        else
        {
          std::string esname = getEmbedName(parent);
          if (esname == "ite")
          {
            // the condition is stored at position 2, after op and deep
            // embedding the branches have no context
            // TODO: maybe they should have SMT context???
            tk = i == 2 ? TermContextKind::SMT_BUILTIN : TermContextKind::NONE;
          }
          else if (esname == "eo.SmtTerm.arg1")
          {
            // corner case: the selector of terms is SMT
            tk = TermContextKind::SMT_GUARDED;
          }
          else if (esname == "eo.SmtType.arg1")
          {
            // corner case: the selector of terms is SMT
            tk = TermContextKind::SMT_TYPE_GUARDED;
          }
          else if (esname == "eo.SmtValue.arg1")
          {
            // corner case: the selector of terms is SMT
            tk = TermContextKind::SMT_VALUE_GUARDED;
          }
          else
          {
            Assert(esname != "=") << "Use smt_apply_= instead";
            tk = TermContextKind::SMT_BUILTIN;
          }
        }
      }
      else if (sname.compare(0, 10, "$smt_type_") == 0)
      {
        tk = TermContextKind::SMT_TYPE;
      }
      else if (sname == "$smd_eo.SmtTerm")
      {
        tk = TermContextKind::SMT;
      }
      else if (sname == "$smd_eo.SmtType")
      {
        tk = TermContextKind::SMT_TYPE;
      }
      else if (sname.compare(0, 8, "$smd_sm.") == 0)
      {
        tk = TermContextKind::SMT_BUILTIN;
      }
      else if (sname.compare(0, 9, "$smd_tsm.") == 0)
      {
        tk = TermContextKind::SMT_TYPE;
      }
      else if (sname.compare(0, 9, "$smd_vsm.") == 0)
      {
        if (sname=="$smd_vsm.Term")
        {
          tk = TermContextKind::SMT;
        }
        else if (sname=="$smd_vsm.Map")
        {
          tk = i==0 ? TermContextKind::SMT_TYPE : TermContextKind::SMT_MAP;
        }
      }
      else if (sname == "$eo_Var")
      {
        tk = i == 1 ? TermContextKind::SMT_BUILTIN : TermContextKind::EUNOIA;
      }
    }
  }
  else if (k == Kind::APPLY)
  {
    if (isProgramApp(parent))
    {
      if (i == 0)
      {
        // the program head has no context
        return TermContextKind::NONE;
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
    tk = TermContextKind::EUNOIA;
  }
  else if (k == Kind::EVAL_IF_THEN_ELSE || k == Kind::EVAL_IS_OK
           || k == Kind::EVAL_REQUIRES)
  {
    // all remaining builtins assume Eunoia arguments
    tk = TermContextKind::EUNOIA;
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

TermContextKind SmtMetaReduce::getMetaKindReturn(const Expr& child,
                                                 TermContextKind parentCtx)
{
  std::vector<Expr> appArgs;
  return getMetaKindReturn(child, appArgs, parentCtx);
}

TermContextKind SmtMetaReduce::getMetaKindReturn(const Expr& child,
                                                 std::vector<Expr>& appArgs,
                                                 TermContextKind parentCtx)
{
  Assert(!child.isNull()) << "null term for meta kind";
  TermContextKind tk = TermContextKind::NONE;
  Expr hd = child;
  // if an apply, we look for the head, this will determine eo.Apply vs.
  // sm.Apply
  while (hd.getKind() == Kind::APPLY && !isProgramApp(hd))
  {
    appArgs.push_back(hd[1]);
    hd = hd[0];
  }
  Kind k = hd.getKind();
  // check for programs
  if (k == Kind::APPLY)
  {
    Assert(isProgramApp(hd));
    // if program app, depends on the type of the program
    Expr p = hd[0];
    Expr ptype = d_tc.getType(p);
    Assert(ptype.getKind() == Kind::PROGRAM_TYPE);
    // convert the type to a metakind
    tk = getTypeMetaKind(ptype[ptype.getNumChildren() - 1]);
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
        tk = TermContextKind::SMT_BUILTIN;
      }
      else
      {
        std::string esname = getEmbedName(child);
        if (esname == "eo.SmtTerm.arg1")
        {
          // Corner case: the selector for SMT terms.
          tk = TermContextKind::SMT;
        }
        else if (esname == "eo.SmtType.arg1")
        {
          // Corner case: the selector for SMT types.
          tk = TermContextKind::SMT_TYPE;
        }
        else if (esname == "eo.SmtValue.arg1")
        {
          // Corner case: the selector for SMT values.
          tk = TermContextKind::SMT_VALUE;
        }
        else if (esname == "vsm.Term.arg1")
        {
          // Corner case: the selector for terms in SMT values.
          tk = TermContextKind::SMT;
        }
        else if (esname == "ite")
        {
          Assert(child.getNumChildren() == 5);
          tk = getMetaKindReturn(child[3], parentCtx);
          Assert(tk == getMetaKindReturn(child[4], parentCtx))
              << "ITE branches have different meta types " << child;
        }
        else if (esname == "=")
        {
          TermContextKind k1 = getMetaKindReturn(child[2], parentCtx);
          TermContextKind k2 = getMetaKindReturn(child[3], parentCtx);
          Assert(k1 == k2) << "Equal sides have different meta types " << child
                           << " " << termContextKindToString(k1) << " "
                           << termContextKindToString(k2);
          tk = TermContextKind::SMT_BUILTIN;
        }
        else
        {
          tk = TermContextKind::SMT_BUILTIN;
        }
      }
    }
    else if (sname.compare(0, 10, "$smt_type_") == 0)
    {
      tk = TermContextKind::SMT_TYPE;
    }
    else if (sname.compare(0, 8, "$smd_eo.") == 0 || sname == "$eo_Var")
    {
      tk = TermContextKind::EUNOIA;
    }
    else if (sname.compare(0, 8, "$smd_sm.") == 0)
    {
      tk = TermContextKind::SMT;
    }
    else if (sname.compare(0, 9, "$smd_tsm.") == 0)
    {
      tk = TermContextKind::SMT_TYPE;
    }
    else if (sname.compare(0, 9, "$smd_vsm.") == 0)
    {
      tk = TermContextKind::SMT_VALUE;
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
    tk = TermContextKind::EUNOIA;
  }
  else if (isLiteral(k))
  {
    tk = TermContextKind::EUNOIA;
  }
  else if (k == Kind::PROGRAM_CONST)
  {
    tk = TermContextKind::PROGRAM;
  }
  else if (k == Kind::FUNCTION_TYPE || k == Kind::TYPE)
  {
    // for now, function type is assumed to be Eunoia.
    // likely HO smt would change this.
    tk = TermContextKind::EUNOIA;
  }
  else if (k == Kind::EVAL_IF_THEN_ELSE || k == Kind::EVAL_IS_OK
           || k == Kind::EVAL_REQUIRES)
  {
    tk = TermContextKind::EUNOIA;
  }
  else if (hd.getNumChildren() == 0)
  {
    std::string sname = getName(hd);
    // Nullary deep embedding constructors
    if (sname.compare(0, 8, "$smd_eo.") == 0 || sname == "$eo_Var")
    {
      tk = TermContextKind::EUNOIA;
    }
    else if (sname.compare(0, 8, "$smd_sm.") == 0)
    {
      tk = TermContextKind::SMT;
    }
    else if (sname.compare(0, 9, "$smd_tsm.") == 0)
    {
      tk = TermContextKind::SMT_TYPE;
    }
    else if (sname.compare(0, 9, "$smd_vsm.") == 0)
    {
      tk = TermContextKind::SMT_VALUE;
    }
    else
    {
      Expr htype = d_tc.getType(hd);
      Assert(!htype.isNull()) << "Failed to type check " << hd;
      tk = getTypeMetaKind(htype);
      // std::cout << "Type for atomic term " << hd << " (" << k << ") is "
      //           << htype << ", thus context is " <<
      //           termContextKindToString(tk)
      //           << std::endl;
      //  if it is a Eunoia constant, it depends on the mapping to
      //  datatypes, accessible via the $eo_get_meta_type method.
      if (k == Kind::CONST && tk == TermContextKind::EUNOIA)
      {
        // std::cout << "...consult meta-kind side condition" << std::endl;
        //  constants are managed by the Eunoia side condition
        Expr mapp = d_state.mkExprSimple(Kind::APPLY, {d_eoGetMetaKind, hd});
        Ctx ectx;
        Expr mm = d_tc.evaluate(mapp.getValue(), ectx);
        tk = getTypeMetaKind(mm);
        if (tk == TermContextKind::NONE && parentCtx != TermContextKind::NONE)
        {
          // otherwise just use the parent type????
          tk = parentCtx;
        }
        // std::cout << "...evaluate meta-kind side condition returns " << mm
        //           << ", which is " << termContextKindToString(tk) <<
        //           std::endl;
      }
      else if (parentCtx != TermContextKind::NONE)
      {
        // otherwise trust the parent kind???
        tk = parentCtx;
      }
    }
  }
  else
  {
    Assert(false) << "Unknown apply term kind for getMetaKindReturn: " << k;
  }
  return tk;
}

std::vector<TermContextKind> SmtMetaReduce::getMetaKindArgs(
    const Expr& parent, TermContextKind parentCtx)
{
  std::vector<TermContextKind> args;
  std::cout << "  MetaArg: " << parent << " / "
            << termContextKindToString(parentCtx) << std::endl;
  for (size_t i = 0, nchild = parent.getNumChildren(); i < nchild; i++)
  {
    TermContextKind ctx = getMetaKindArg(parent, i, parentCtx);
    std::cout << "    MetaArgChild: " << termContextKindToString(ctx) << " for "
              << parent[i] << std::endl;
    args.push_back(ctx);
  }
  std::cout << "  MetaArg: end" << std::endl;
  return args;
}

}  // namespace ethos
