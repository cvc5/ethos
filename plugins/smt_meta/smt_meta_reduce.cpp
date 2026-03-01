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

SmtMetaReduce::SmtMetaReduce(State& s) : StdPlugin(s), d_smSygus(s)
{
  d_prefixToMetaKind["eo"] = MetaKind::EUNOIA;
  d_prefixToMetaKind["sm"] = MetaKind::SMT;
  d_prefixToMetaKind["tsm"] = MetaKind::SMT_TYPE;
  d_prefixToMetaKind["vsm"] = MetaKind::SMT_VALUE;
  d_prefixToMetaKind["msm"] = MetaKind::SMT_MAP;
  d_prefixToMetaKind["ssm"] = MetaKind::SMT_SEQ;
  d_prefixToMetaKind["dt"] = MetaKind::DATATYPE;
  d_prefixToMetaKind["dtc"] = MetaKind::DATATYPE_CONSTRUCTOR;
  d_typeToMetaKind["$eo_Type"] = MetaKind::EUNOIA;
  // d_typeToMetaKind["$eo_Proof"] = MetaKind::PROOF;
  d_typeToMetaKind["$smt_Term"] = MetaKind::SMT;
  d_typeToMetaKind["$smt_Type"] = MetaKind::SMT_TYPE;
  d_typeToMetaKind["$smt_Value"] = MetaKind::SMT_VALUE;
  d_typeToMetaKind["$smt_Map"] = MetaKind::SMT_MAP;
  d_typeToMetaKind["$smt_Seq"] = MetaKind::SMT_SEQ;
  d_typeToMetaKind["$smt_Datatype"] = MetaKind::DATATYPE;
  d_typeToMetaKind["$smt_DatatypeCons"] = MetaKind::DATATYPE_CONSTRUCTOR;
  d_typeToMetaKind["$smt_BuiltinType"] = MetaKind::SMT_BUILTIN;

  if (StdPlugin::optionSmtMetaSygusGrammar())
  {
    d_smSygus.initializeGrammars();
  }
}

SmtMetaReduce::~SmtMetaReduce() {}

MetaKind SmtMetaReduce::prefixToMetaKind(const std::string& str) const
{
  std::map<std::string, MetaKind>::const_iterator it =
      d_prefixToMetaKind.find(str);
  if (it != d_prefixToMetaKind.end())
  {
    return it->second;
  }
  return MetaKind::EUNOIA;
  // Assert(false) << "Bad prefix \"" << str << "\"";
  // return MetaKind::NONE;
}

bool SmtMetaReduce::printMetaType(const Expr& t,
                                  std::ostream& os,
                                  MetaKind tctx) const
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
    case MetaKind::SMT_SEQ: os << "ssm.Seq"; break;
    case MetaKind::DATATYPE: os << "dt.Datatype"; break;
    case MetaKind::DATATYPE_CONSTRUCTOR: os << "dtc.DatatypeCons"; break;
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
  if (k == Kind::PROGRAM_CONST)
  {
    // programs always print verbatim
    os << c;
    return;
  }
  if (k == Kind::CONST)
  {
    std::string cname = getName(c);
    // if it is an explicit embedding of a datatype, take the suffix
    if (cname.compare(0, 5, "$emb_") == 0)
    {
      size_t firstDot = cname.find('.');
      if (firstDot == std::string::npos)
      {
        os << "eo.";
      }
      os << cname.substr(5);
    }
    else
    {
      MetaKind k = getMetaKind(d_state, c, cname);
      os << metaKindToPrefix(k) << cname;
    }
  }
  else if (k == Kind::BOOL_TYPE)
  {
    os << "eo.Bool";
  }
  else
  {
    const Literal* l = c.getValue()->asLiteral();
    if (l == nullptr)
    {
      Assert(false) << "Unknown atomic term kind " << k;
      return;
    }
    if (k == Kind::BOOLEAN)
    {
      os << "(eo.Boolean " << (l->d_bool ? "true" : "false") << ")";
    }
    else if (k == Kind::NUMERAL)
    {
      os << "(eo.Numeral ";
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
    }
    else if (k == Kind::RATIONAL)
    {
      os << "(eo.Rational " << c << ")";
    }
    else if (k == Kind::BINARY)
    {
      os << "(eo.Binary ";
      const BitVector& bv = l->d_bv;
      const Integer& bvi = bv.getValue();
      os << bv.getSize() << " " << bvi.toString() << ")";
    }
    else if (k == Kind::STRING)
    {
      os << "(eo.String " << c << ")";
    }
    else
    {
      Assert(false) << "Unknown atomic term literal kind " << k;
    }
  }
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
    bool isFunType = (ck == Kind::FUNCTION_TYPE);
    size_t printArgStart = 0;
    // Trace("smt-meta") << "  patMatch: " << tcur << " / " << currTerm << " / "
    //           << metaKindToString(parent) << " / kind " << ck
    //           << std::endl;
    if (ck == Kind::APPLY)
    {
      Assert(tcur[0].getKind()!=Kind::PROGRAM) << "Cannot match on program " << tcur[0];
      Assert(tcur.getNumChildren() == 2);
      // Determine if this is a Eunoia internal term, or an
      // SMT term eagerly here
      // Use the appropriate prefix
      cname << "eo.Apply";
      printArgs = true;
    }
    else if (ck == Kind::FUNCTION_TYPE)
    {
      // we handle function in a special case below.
      cname << "eo.Apply";
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
      for (size_t i = printArgStart, nchild = tcur.getNumChildren(); i < nchild;
           i++)
      {
        std::stringstream ssNext;
        ssNext << "(" << cname.str() << ".arg" << (i + 1 - printArgStart) << " "
               << currTerm << ")";
        // special case: since (-> T U) is (_ (_ -> T) U)
        if (i == 0 && isFunType)
        {
          std::stringstream testera;
          testera << "((_ is eo.Apply) " << ssNext.str() << ")";
          print.push(testera.str());
          std::stringstream testerf;
          testerf << "((_ is eo.FunType) (eo.Apply.arg1 " << ssNext.str()
                  << "))";
          print.push(testerf.str());
          std::stringstream ssNext2;
          ssNext2 << "(eo.Apply.arg2 " << ssNext.str() << ")";
          visit.emplace_back(tcur[i], ssNext2.str(), MetaKind::EUNOIA);
        }
        else
        {
          // the next type is "reset"
          visit.emplace_back(tcur[i], ssNext.str(), MetaKind::EUNOIA);
        }
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
        // Trace("smt-meta") << "PAT-MATCH: " << currTerm
        //           << " was matched in term context "
        //           << metaKindToString(parent) << std::endl;
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
      Assert(d_state.getConstructorKind(tcur.getValue()) != Attr::AMB)
          << "Matching on amb " << tcur;
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
  return (sname.compare(0, 5, "$emb_") == 0);
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
  Assert(oApp.getKind() == Kind::APPLY_OPAQUE)
      << "Bad kind for opaque " << oApp.getKind() << " " << oApp;
  std::string aname = getName(oApp[0]);
  if (!isSmtApplyApp(oApp))
  {
    Assert(false) << "Expected smt apply app when asking for embed name "
                  << oApp;
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
  std::map<std::pair<Expr, MetaKind>, bool> pushedChildren;
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
    if (pushedChildren.find(key) != pushedChildren.end())
    {
      if (itc != cparen.end())
      {
        // NONE context means done with arguments, close the pending parens
        for (size_t i = 0; i < itc->second; i++)
        {
          os << ")";
        }
        cparen.erase(key);
      }
      pushedChildren.erase(key);
      visit.pop_back();
      continue;
    }
    pushedChildren[key] = true;
    // otherwise, we check for a change of context and insert a cast if
    // necessary compute the child context
    Kind ck = recTerm.getKind();

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
      continue;
    }
    else if (recTerm.getNumChildren() == 0 && ck != Kind::VARIABLE)
    {
      // atomic terms print here
      // We handle SMT vs SMT_BUILTIN within that method
      // Trace("smt-meta") << "print emb atomic term: " << recTerm << std::endl;
      printEmbAtomicTerm(recTerm, os);
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
        if (StdPlugin::optionFlattenEval() || !recTerm.isEvaluatable())
        {
          // Note that we use eo.Apply unguarded. In particular, the
          // flatten-eval step has ensured that constructing Eunoia terms
          // in this way will not get stuck during term construction, but
          // instead at program invocation.
          os << "eo.Apply ";
        }
        else
        {
          // Otherwise, we must propagate stuckness using the mk apply program.
          os << "$eo_mk_apply ";
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
        if (recTerm.getNumChildren() > 2)
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
      os << "(eo.Apply (eo.Apply eo.FunType ";
      cparen[key]++;
      // proactively insert a parenthesis after the first argument based on
      // the curried apply above.
      std::pair<Expr, MetaKind> fwdKey(recTerm[0], MetaKind::EUNOIA);
      cparen[fwdKey]++;
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
        Assert(false) << "Bad name for literal kind " << ck << std::endl;
      }
    }
    else if (ck == Kind::VARIABLE)
    {
      const Literal* l = recTerm.getValue()->asLiteral();
      os << "(eo.Var \"" << l->toString() << "\" ";
      Expr recTermT = d_tc.getType(recTerm);
      visit.emplace_back(recTermT, MetaKind::EUNOIA);
      cparen[key] += 1;
      continue;
    }
    else
    {
      Assert(false) << "Unhandled kind in print term " << ck << " " << recTerm
                    << " / " << metaKindToString(parent) << std::endl;
    }
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
      MetaKind ctxRec = MetaKind::EUNOIA;
      visit.emplace_back(rc, ctxRec);
    }
  } while (!visit.empty());
  return true;
}

void SmtMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  finalizeProgram(v, prog);
}

void SmtMetaReduce::finalizeProgram(const Expr& v,
                                    const Expr& prog,
                                    bool isDefine)
{
  // check for duplicate forward declaration, ignore
  if (prog.isNull() && d_progDeclProcessed.find(v) != d_progDeclProcessed.end())
  {
    return;
  }
  std::string vname = getName(v);
  Trace("smt-meta") << "*** Setting up program " << v << " / " << !prog.isNull()
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
  // Trace("smt-meta") << "Type is " << vt << std::endl;
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
    Trace("smt-meta") << "Print meta type " << vt[i - 1] << std::endl;
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
  // Trace("smt-meta") << "DECLARE " << decl.str() << std::endl;
  //  if forward declared, we are done for now
  if (prog.isNull())
  {
    d_progDeclProcessed.insert(v);
    d_defs << decl.str() << std::endl;
    return;
  }
  Trace("smt-meta") << "*** FINALIZE " << v << std::endl;
  bool reqAxiom = (d_progDeclProcessed.find(v) != d_progDeclProcessed.end());
  // compile the pattern matching
  std::stringstream cases;
  std::stringstream casesEnd;
  // If the return type does not have meta-kind Eunoia, then it cannot get
  // stuck. We ensure that all programs over such types are total.
  // We also are not a Eunoia program if we called this method via a define
  // command.
  bool isEunoiaProgram =
      (getTypeMetaKind(vt[nargs - 1]) == MetaKind::EUNOIA) && !isDefine;
  // start with stuck case, if not a SMT program
  if (isEunoiaProgram)
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
      Trace("smt-meta") << std::endl
                        << "; Print pat matching for " << hd[j]
                        << " in context " << metaKindToString(ctxPatMatch)
                        << std::endl;
      printEmbPatternMatch(
          hd[j], args[j - 1], currCase, ctx, print, ctxPatMatch);
      Trace("smt-meta") << "...returns \"" << currCase.str() << "\""
                        << std::endl;
    }
    // compile the return for this case
    std::stringstream currRet;
    // The type of the function determines the initial context of return terms
    // we print
    MetaKind bodyInitCtx = vctxArgs[nargs - 1];
    Trace("smt-meta") << std::endl
                      << "; Print body " << body << " in context "
                      << metaKindToString(bodyInitCtx) << std::endl;
    printEmbTerm(body, currRet, ctx, bodyInitCtx);
    Trace("smt-meta") << "...returns \"" << currRet.str() << "\"" << std::endl;
    // for SMT programs, the last case is assumed to be total
    // this is part of the trusted core: to ensure all programs in
    // model_smt.eo are total.
    if (i + 1 < ncases || isEunoiaProgram)
    {
      cases << "  (ite ";
      print.printConjunction(cases);
      cases << std::endl;
      casesEnd << ")";
    }
    else
    {
      // note we can't do this assertion since some programs e.g.
      // $smtx_msm_lookup have exhaustive cases with no explicit default case
      // Assert (print.empty()) << "Non-trivial base case for non-Eunoia program
      // " << v;
    }
    cases << "    " << currRet.str() << std::endl;
  }
  // axiom
  if (reqAxiom)
  {
    // declare now if not already forward declared
    if (d_progDeclProcessed.find(v) == d_progDeclProcessed.end())
    {
      d_defs << decl.str();
    }
    d_defs << "(assert (! (forall (" << varList.str() << ")" << std::endl
           << "  ";
    if (StdPlugin::optionSmtMetaUseTriggers())
    {
      d_defs << "(! ";
    }
    d_defs << "(= " << appTerm.str() << std::endl;
    casesEnd << ")";
  }
  else
  {
    d_defs << "(define-fun " << v << " (" << varList.str() << ") "
           << retType.str() << std::endl;
  }
  d_defs << cases.str();
  if (isEunoiaProgram)
  {
    d_defs << "    eo.Stuck";
  }
  d_defs << casesEnd.str();
  if (reqAxiom)
  {
    if (StdPlugin::optionSmtMetaUseTriggers())
    {
      d_defs << " :pattern (" << appTerm.str() << "))";
    }
    d_defs << ") :named sm.axiom." << v << ")";
  }
  d_defs << ")" << std::endl;
  d_defs << std::endl;
}

void SmtMetaReduce::define(const std::string& name, const Expr& e)
{
  // NOTE: the code here ensures that we preserve definitions for the final vc.
  // This is required since we do not replace e.g. eo::list_concat with
  // $eo_list_concat until the final generation of smt2. This means that this
  // definition (although it would have been inlined) is still necessary to
  // define what eo::list_concat will desugar to. Also note this definition is
  // properly preserved by trim_defs which is agnostic to eo:: vs $eo_.
  if (name.compare(0, 4, "$eo_") == 0)
  {
    Expr p = e;
    if (p.getKind() == Kind::LAMBDA)
    {
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
      // Expr retType = d_tc.getType(body);
      Trace("smt-meta") << "Look at define " << name << std::endl;
      // if we fail to type check, just allocate a type variable
      // retType = retType.isNull() ? allocateTypeVariable() : retType;
      Expr retType = allocateTypeVariable();
      Expr pt = d_state.mkProgramType(argTypes, retType);
      Trace("smt-meta") << "....make program " << name
                        << " for define, prog type is " << pt << std::endl;
      // Expr pt = d_state.mkBuiltinType(Kind::LAMBDA);
      Expr tmp = d_state.mkSymbol(Kind::PROGRAM_CONST, name, pt);
      // We need to preserve definitions in the final VC.
      // We reduce defines to a program e.g.
      // (define foo ((x T)) (bar x))
      //   becomes
      // (program foo ((x T))
      //   :signature (T) (eo::typeof (bar x))
      //   (
      //   ((foo x) (bar x))
      //   )
      // )
      std::vector<Expr> appChildren;
      appChildren.push_back(tmp);
      for (size_t i = 0, nargs = e[0].getNumChildren(); i < nargs; i++)
      {
        appChildren.push_back(e[0][i]);
      }
      Expr progApp = d_state.mkExprSimple(Kind::APPLY, appChildren);
      Expr pcase = d_state.mkPair(progApp, e[1]);
      Expr prog = d_state.mkExprSimple(Kind::PROGRAM, {pcase});
      Trace("smt-meta") << "...do program " << tmp << " / " << prog
                        << " instead" << std::endl;
      finalizeProgram(tmp, prog, true);
      Trace("smt-meta") << "...finished lambda program" << std::endl;
    }
    else
    {
      d_defs << "(define-fun " << name << " () eo.Term";
      d_defs << " ";
      SelectorCtx ctx;
      printEmbTerm(p, d_defs, ctx);
      d_defs << ")" << std::endl;
    }
  }
}

void SmtMetaReduce::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  finalizeDecl(e);
}

void SmtMetaReduce::finalizeDecl(const Expr& e)
{
  if (d_declSeen.find(e) != d_declSeen.end())
  {
    return;
  }
  d_declSeen.insert(e);
  // first, determine which datatype (if any) this belongs to
  std::stringstream ss;
  ss << e;
  std::string sname = ss.str();
  std::stringstream* out = nullptr;
  std::stringstream cname;
  // get the meta-kind based on its name
  std::string cnamek;
  MetaKind tk = getMetaKind(d_state, e, cnamek);
  if (tk == MetaKind::EUNOIA)
  {
    cname << "eo." << cnamek;
    out = &d_embedEoTermDt;
  }
  else if (tk == MetaKind::SMT_TYPE)
  {
    cname << "tsm." << cnamek;
    out = &d_embedTypeDt;
  }
  else if (tk == MetaKind::SMT)
  {
    cname << "sm." << cnamek;
    out = &d_embedTermDt;
  }
  else if (tk == MetaKind::SMT_VALUE)
  {
    cname << "vsm." << cnamek;
    out = &d_embedValueDt;
  }
  else if (tk == MetaKind::SMT_MAP)
  {
    cname << "msm." << cnamek;
    out = &d_embedMapDt;
  }
  else if (tk == MetaKind::SMT_SEQ)
  {
    cname << "ssm." << cnamek;
    out = &d_embedSeqDt;
  }
  if (out == nullptr)
  {
    Trace("smt-meta") << "Do not include " << e << std::endl;
    return;
  }
  Trace("smt-meta") << "Include " << e << std::endl;
  (*out) << "  ; " << (isEmbedCons(e) ? "smt-cons: " : "user-decl: ") << cnamek
         << std::endl;
  Expr c = e;
  Expr ct = d_tc.getType(c);
  // (*out) << "  ; type is " << ct << std::endl;
  Attr attr = d_state.getConstructorKind(e.getValue());
  // (*out) << "  ; attr is " << attr << std::endl;
  (*out) << "  (";
  (*out) << cname.str();
  size_t nopqArgs = 0;
  Expr retType = ct;
  if (attr == Attr::OPAQUE)
  {
    // opaque symbols are non-nullary constructors
    Assert(ct.getKind() == Kind::FUNCTION_TYPE);
    nopqArgs = ct.getNumChildren() - 1;
    retType = ct[nopqArgs];
  }
  AlwaysAssert(attr != Attr::AMB && attr != Attr::AMB_DATATYPE_CONSTRUCTOR);
  std::stringstream sygusArgs;
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
    if (!printMetaType(typ, sst))
    {
      // Assert(false) << "Failed to get meta-type for " << e;
      // os << e;
      //  otherwise, a user-provided ambiguous or opaque term, use eo_Term
      sst << "eo.Term";
    }
    (*out) << sst.str();
    sygusArgs << " G_" << sst.str();
    //(*out) << "; Printing datatype argument type " << typ << " gives \"" <<
    // sst.str() << "\" " << termKindToString(tk) << std::endl;
    (*out) << ")";
  }
  (*out) << ")" << std::endl;
  std::stringstream gruleBase;
  if (nopqArgs > 0)
  {
    gruleBase << "(" << cname.str() << sygusArgs.str() << ")";
  }
  else
  {
    gruleBase << cname.str();
  }
  d_smSygus.addGrammarRules(e, cnamek, tk, gruleBase.str(), retType);
}

void SmtMetaReduce::finalize()
{
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
  // TODO: this is only necessary for the old version
  if (d_embedTypeDt.str().empty())
  {
    d_embedTypeDt << "  (tsm.None)" << std::endl;
  }
  if (d_embedTermDt.str().empty())
  {
    d_embedTermDt << "  (sm.None)" << std::endl;
  }
  if (d_embedMapDt.str().empty())
  {
    d_embedMapDt << "  (msm.None)" << std::endl;
  }
  if (d_embedSeqDt.str().empty())
  {
    d_embedSeqDt << "  (ssm.None)" << std::endl;
  }
  replace(finalSm, "$SM_TYPE_DECL$", d_embedTypeDt.str());
  replace(finalSm, "$SM_TERM_DECL$", d_embedTermDt.str());
  replace(finalSm, "$SM_VALUE_DECL$", d_embedValueDt.str());
  replace(finalSm, "$SM_MAP_DECL$", d_embedMapDt.str());
  replace(finalSm, "$SM_SEQ_DECL$", d_embedSeqDt.str());
  replace(finalSm, "$SM_EO_TERM_DECL$", d_embedEoTermDt.str());

  std::stringstream sso;
  sso << s_plugin_path << "plugins/smt_meta/smt_meta_gen.smt2";
  Trace("smt-meta") << "Write smt2-defs " << sso.str() << std::endl;
  std::ofstream out(sso.str());
  out << finalSm;
}

bool SmtMetaReduce::echo(const std::string& msg)
{
  std::cout << "ECHO " << msg << std::endl;
  if (msg.compare(0, 9, "smt-meta ") == 0)
  {
    std::string eosc = msg.substr(9);
    size_t pos = eosc.find(' ');
    if (pos != std::string::npos)
    {
      eosc.erase(pos);  // erase from the space to the end
    }
    Expr vv = d_state.getVar(eosc);
    if (vv.isNull())
    {
      Assert(false)
          << "When making verification condition, could not find program "
          << eosc;
    }
    Expr def = d_state.getProgram(vv.getValue());
    Assert(!def.isNull());
    Expr patCall = def[0][0];
    Assert(!patCall.isNull());
    d_smtVc << ";;;; final verification condition for " << eosc << std::endl;
    // NOTE: this is intentionally quantifying on sm.Term, not eo.Term.
    // In other words, this conjectures that there is an sm.Term, that
    // when embedded into Eunoia witnesses the unsoundness.
    Expr vt = d_tc.getType(vv);
    std::stringstream varList;
    std::stringstream eoTrue;
    std::stringstream call;
    eoTrue << "(eo.Boolean true)";
    Assert(vt.getKind() == Kind::PROGRAM_TYPE);
    Assert(patCall.getNumChildren() == vt.getNumChildren());
    size_t nargs = vt.getNumChildren();
    ConjectureType ctype = StdPlugin::optionSmtMetaConjectureType();
    if (ctype == ConjectureType::VC)
    {
      std::stringstream conjEnd;
      if (!StdPlugin::optionSmtMetaDebugConjecture())
      {
        d_smtVc << "(assert (! (exists (";
        conjEnd << ")";
      }
      for (size_t i = 1; i < nargs; i++)
      {
        if (StdPlugin::optionSmtMetaDebugConjecture())
        {
          d_smtVc << "(declare-const x" << i << " eo.Term)" << std::endl;
        }
        else
        {
          if (i > 1)
          {
            d_smtVc << " ";
          }
          d_smtVc << "(x" << i << " eo.Term)";
        }
        call << " x" << i;
      }
      if (StdPlugin::optionSmtMetaDebugConjecture())
      {
        d_smtVc << "(assert (! ";
      }
      else
      {
        d_smtVc << ")" << std::endl << "  ";
      }
      d_smtVc << "(= (" << eosc << call.str() << ") " << eoTrue.str() << ")";
      d_smtVc << conjEnd.str();
      d_smtVc << " :named sm.conjecture." << vv << ")";
      d_smtVc << ")" << std::endl;
      d_smtVc << "(check-sat)" << std::endl;
      if (StdPlugin::optionSmtMetaDebugConjecture())
      {
        d_smtVc << "(get-model)" << std::endl;
        d_smtVc << "(get-value (" << call.str() << "))" << std::endl;
      }
    }
    else if (ctype == ConjectureType::SYGUS)
    {
      d_smSygus.finalizeGrammars();
      for (size_t i = 1; i < nargs; i++)
      {
        std::stringstream varName;
        varName << "arg_" << patCall[i];
        d_smtVc << "(synth-fun " << varName.str() << " () eo.Term";
        if (StdPlugin::optionSmtMetaSygusGrammar())
        {
          d_smSygus.printGrammar(varName.str(), vt[i - 1], d_smtVc);
        }
        d_smtVc << ")" << std::endl;
        call << " " << varName.str();
      }
      d_smtVc << "(constraint ";
      d_smtVc << "(= (" << eosc << call.str() << ") " << eoTrue.str() << ")";
      d_smtVc << ")" << std::endl;
      d_smtVc << "(check-synth)" << std::endl;
    }
    else
    {
      Assert(false) << "Unknown conjecture type";
    }
    return false;
  }
  else if (msg.compare(0, 13, "smt-meta-cmd ") == 0)
  {
    std::string eosc = msg.substr(13);
    d_defs << "(echo \"Run " << eosc << "...\")" << std::endl;
    d_defs << eosc << std::endl;
    return false;
  }
  return true;
}

MetaKind SmtMetaReduce::getTypeMetaKind(const Expr& typ,
                                        MetaKind elseKind) const
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
  if (k == Kind::FUNCTION_TYPE)
  {
    return getTypeMetaKind(typ[typ.getNumChildren() - 1], elseKind);
  }
  std::string sname = getName(typ);
  std::map<std::string, MetaKind>::const_iterator it =
      d_typeToMetaKind.find(sname);
  if (it != d_typeToMetaKind.end())
  {
    return it->second;
  }
  return elseKind;
}

MetaKind SmtMetaReduce::getMetaKind(State& s,
                                    const Expr& e,
                                    std::string& cname) const
{
  std::string sname = getName(e);
  if (sname.compare(0, 5, "$smt_") == 0 || sname == "$eo_Term")
  {
    // internal-only symbol, e.g. one used for defining the deep embedding
    cname = sname;
    return MetaKind::SMT_BUILTIN;
  }
  // terms starting with @@ are considered Eunoia (not SMT-LIB).
  // all symbols apart from $eo_Term that begin with $eo_ are Eunoia terms,
  // e.g. $eo_Var, $eo_List, etc.
  if (sname.compare(0, 2, "@@") == 0 || sname.compare(0, 4, "$eo_") == 0)
  {
    cname = sname;
    return MetaKind::EUNOIA;
  }
  else if (sname.compare(0, 5, "$emb_") == 0)
  {
    size_t firstDot = sname.find('.');
    if (firstDot == std::string::npos)
    {
      cname = sname.substr(5);
      return MetaKind::EUNOIA;
    }
    std::string prefix = sname.substr(5, firstDot - 5);
    cname = sname.substr(firstDot + 1);
    return prefixToMetaKind(prefix);
  }
  cname = sname;
  return MetaKind::EUNOIA;
}

bool SmtMetaReduce::isProgramApp(const Expr& app)
{
  return (app.getKind() == Kind::APPLY
          && app[0].getKind() == Kind::PROGRAM_CONST);
}


}  // namespace ethos
