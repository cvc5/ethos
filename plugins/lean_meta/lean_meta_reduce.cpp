/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "lean_meta_reduce.h"

#include <fstream>
#include <sstream>
#include <string>

#include "../linear_patterns/linear_patterns.h"
#include "state.h"

namespace ethos {

LeanMetaReduce::LeanMetaReduce(State& s) : MetaReducePlugin(s)
{
  d_typeToMetaKind["$eo_Term"] = MetaKind::EUNOIA;
  d_typeToMetaKind["$eo_Proof"] = MetaKind::PROOF;
  d_typeToMetaKind["$eo_State"] = MetaKind::CHECKER_STATE;
  d_typeToMetaKind["$eo_StateObj"] = MetaKind::CHECKER_STATE_OBJ;
  d_typeToMetaKind["$eo_Index"] = MetaKind::CHECKER_INDEX;
  d_typeToMetaKind["$eo_IndexList"] = MetaKind::CHECKER_INDEX_LIST;
  d_typeToMetaKind["$eo_Rule"] = MetaKind::CHECKER_RULE;
  d_typeToMetaKind["$eo_Cmd"] = MetaKind::CHECKER_CMD;
  d_typeToMetaKind["$eo_CmdList"] = MetaKind::CHECKER_CMD_LIST;
  d_typeToMetaKind["$eo_ArgList"] = MetaKind::CHECKER_ARG_LIST;
  d_prefixToMetaKind["s"] = MetaKind::CHECKER_STATE;
  d_prefixToMetaKind["so"] = MetaKind::CHECKER_STATE_OBJ;
  d_prefixToMetaKind["r"] = MetaKind::CHECKER_RULE;
  d_prefixToMetaKind["cmd"] = MetaKind::CHECKER_CMD;
  d_prefixToMetaKind["cmdl"] = MetaKind::CHECKER_CMD_LIST;
  d_prefixToMetaKind["indl"] = MetaKind::CHECKER_INDEX_LIST;
  d_prefixToMetaKind["al"] = MetaKind::CHECKER_ARG_LIST;
}

LeanMetaReduce::~LeanMetaReduce() {}

bool LeanMetaReduce::isBuiltinMetaSymbol(const std::string& sname) const
{
  return sname.compare(0, 5, "$smt_") == 0
         || d_typeToMetaKind.find(sname) != d_typeToMetaKind.end();
}

bool LeanMetaReduce::printMetaType(const Expr& t,
                                   std::ostream& os,
                                   MetaKind tctx) const
{
  MetaKind tk = getTypeMetaKind(t);
  if (tk == MetaKind::SMT_BUILTIN || tk == MetaKind::SMT_BUILTIN_DATATYPE)
  {
    os << getEmbedName(t, tctx);
    return true;
  }
  return printMetaTypeKind(tk, os);
}

bool LeanMetaReduce::printMetaTypeKind(MetaKind k, std::ostream& os) const
{
  switch (k)
  {
    case MetaKind::EUNOIA: os << "Term"; break;
    case MetaKind::DATATYPE: os << "Datatype"; break;
    case MetaKind::DATATYPE_CONSTRUCTOR: os << "DatatypeCons"; break;
    case MetaKind::SMT_TYPE: os << "SmtType"; break;
    case MetaKind::SMT_MODEL: os << "SmtModel"; break;
    case MetaKind::SMT: os << "SmtTerm"; break;
    case MetaKind::SMT_VALUE: os << "SmtValue"; break;
    case MetaKind::SMT_MAP: os << "SmtMap"; break;
    case MetaKind::SMT_SEQ: os << "SmtSeq"; break;
    case MetaKind::PROOF: os << "Proof"; break;
    case MetaKind::SMT_DATATYPE: os << "SmtDatatype"; break;
    case MetaKind::SMT_DATATYPE_CONSTRUCTOR: os << "SmtDatatypeCons"; break;
    case MetaKind::CHECKER_STATE: os << "CState"; break;
    case MetaKind::CHECKER_STATE_OBJ: os << "CStateObj"; break;
    case MetaKind::CHECKER_INDEX: os << "CIndex"; break;
    case MetaKind::CHECKER_INDEX_LIST: os << "CIndexList"; break;
    case MetaKind::CHECKER_RULE: os << "CRule"; break;
    case MetaKind::CHECKER_CMD: os << "CCmd"; break;
    case MetaKind::CHECKER_CMD_LIST: os << "CCmdList"; break;
    case MetaKind::CHECKER_ARG_LIST: os << "CArgList"; break;
    default: return false;
  }
  return true;
}

void LeanMetaReduce::printEmbAtomicTerm(const Expr& c, std::ostream& os)
{
  Kind k = c.getKind();
  if (k == Kind::TYPE)
  {
    os << "Term.Type";
    return;
  }
  if (c.getKind() == Kind::PROGRAM_CONST)
  {
    // programs always print verbatim
    std::stringstream ss;
    ss << c;
    os << cleanId(ss.str());
    return;
  }
  if (k == Kind::CONST)
  {
    std::string cname;
    MetaKind k = getMetaKind(d_state, c, cname);
    if (cname == "$eo_pf")
    {
      os << "Proof.pf";
    }
    else
    {
      if (!printMetaTypeKind(k, os))
      {
        os << "Term";
      }
      os << "." << cleanSmtId(cname);
    }
  }
  else if (k == Kind::BOOL_TYPE)
  {
    os << "Term.Bool";
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
      os << "(Term.Boolean " << (l->d_bool ? "true" : "false") << ")";
    }
    else if (k == Kind::NUMERAL)
    {
      os << "(Term.Numeral ";
      const Integer& ci = l->d_int;
      if (ci.sgn() == -1)
      {
        const Integer& cin = -ci;
        os << "(-" << cin.toString() << " : eo_lit_Int)";
      }
      else
      {
        os << ci.toString();
      }
      os << ")";
    }
    else if (k == Kind::RATIONAL)
    {
      os << "(Term.Rational ";
      std::stringstream ss;
      ss << c;
      bool isNeg = (l->d_rat.sgn() == -1);
      os << (isNeg ? "(- " : "");
      std::string rstr = ss.str();
      rstr = replace_all(rstr, "/", " ");
      rstr = replace_all(rstr, "-", "");
      os << "(eo_lit_mk_rational " << rstr << ")";
      os << (isNeg ? ")" : "") << ")";
    }
    else if (k == Kind::BINARY)
    {
      os << "(Term.Binary ";
      const BitVector& bv = l->d_bv;
      const Integer& bvi = bv.getValue();
      os << bv.getSize() << " " << bvi.toString() << ")";
    }
    else if (k == Kind::STRING)
    {
      os << "(Term.String " << c << ")";
    }
    else
    {
      Assert(false) << "Unknown atomic term literal kind " << k;
    }
  }
}

bool is_integer(const std::string& s)
{
  if (s.empty()) return false;
  for (unsigned char c : s)
  {
    if (!std::isdigit(c)) return false;
  }
  return true;
}

std::string LeanMetaReduce::getEmbedName(const Expr& oApp, MetaKind ctx)
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
  std::string smtStr = cleanSmtId(l->d_str.toString());
  // literals don't need smt_
  if (is_integer(smtStr) || smtStr == "true" || smtStr == "false"
      || (!smtStr.empty() && smtStr.compare(0, 1, "\"") == 0))
  {
    return smtStr;
  }
  std::stringstream ss;
  ss << (isSmtMetaKind(ctx) ? "smt_lit_" : "eo_lit_") << smtStr;
  return ss.str();
}

void LeanMetaReduce::printEmbTerm(const Expr& body,
                                  std::ostream& os,
                                  MetaKind tinit,
                                  bool maybeLetify)
{
  std::map<const ExprValue*, size_t> lbind;
  if (maybeLetify && d_state.getOptions().d_printDag)
  {
    std::vector<Expr> ll;
    lbind = Expr::computeLetBinding(body, ll);
    std::stringstream osc;
    bool firstTime = true;
    for (const Expr& l : ll)
    {
      // if its just an $smt_apply_0, don't print
      if (isSmtApplyApp(l) && l.getNumChildren() == 2)
      {
        lbind.erase(l.getValue());
        continue;
      }
      if (firstTime)
      {
        os << std::endl;
        firstTime = false;
      }
      const ExprValue* lv = l.getValue();
      size_t id = lbind[lv];
      os << "    let _v" << id << " := ";
      lbind.erase(lv);
      printEmbTermInternal(l, os, tinit, lbind);
      lbind[lv] = id;
      os << std::endl;
    }
    os << (firstTime ? "" : "    ");
  }
  printEmbTermInternal(body, os, tinit, lbind);
}
void LeanMetaReduce::printEmbTermInternal(
    const Expr& body,
    std::ostream& os,
    MetaKind tinit,
    std::map<const ExprValue*, size_t>& lbind)
{
  std::map<Expr, std::string>::const_iterator it;
  std::map<Expr, MetaKind>::const_iterator ittc;
  std::map<std::pair<Expr, MetaKind>, size_t> cparen;
  std::map<std::pair<Expr, MetaKind>, bool> pushedChildren;
  std::map<std::pair<Expr, MetaKind>, size_t>::iterator itc;
  std::map<const ExprValue*, size_t>::iterator itl;
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
    itl = lbind.find(cur.first.getValue());
    if (itl != lbind.end())
    {
      os << "_v" << itl->second;
      if (itc != cparen.end())
      {
        // NONE context means done with arguments, close the pending parens
        for (size_t i = 0; i < itc->second; i++)
        {
          os << ")";
        }
        cparen.erase(key);
      }
      visit.pop_back();
      continue;
    }
    pushedChildren[key] = true;
    // otherwise, we check for a change of context and insert a cast if
    // necessary compute the child context
    Kind ck = recTerm.getKind();
    // Trace("lean-meta") << "print: " << recTerm << " (" << ck << "), "
    //           << metaKindToString(parent) << " / "
    //           << metaKindToString(child) << std::endl;
    // We now should only care about the child context!!!
    // if we are printing the head of the term
    if (ck == Kind::PARAM)
    {
      std::stringstream ssp;
      ssp << recTerm;
      os << cleanSmtId(ssp.str());
      continue;
    }
    else if (recTerm.getNumChildren() == 0 && ck != Kind::VARIABLE)
    {
      // atomic terms print here
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
        if (!recTerm.isEvaluatable())
        {
          // Note that we use eo.Apply unguarded. In particular, the
          // flatten-eval step has ensured that constructing Eunoia terms
          // in this way will not get stuck during term construction, but
          // instead at program invocation.
          os << "Term.Apply ";
        }
        else
        {
          // Otherwise, we must propagate stuckness using the mk apply program.
          os << "__eo_mk_apply ";
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
          || sname.compare(0, 10, "$smt_type_") == 0
          || sname.compare(0, 13, "$smt_datatype") == 0)
      {
        std::string embName = getEmbedName(recTerm, tinit);
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
      os << "(Term.Apply (Term.Apply Term.FunType ";
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
        os << "(__eo_" << kstr.substr(4) << " ";
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
      os << "(Term.Var \"" << l->toString() << "\" ";
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
}

void LeanMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  // forward declaration, ignore
  if (prog.isNull())
  {
    return;
  }
  // must linearize the patterns
  std::vector<std::pair<Expr, Expr>> linProgs =
      LinearPattern::linearize(d_state, v, prog);
  Assert(!linProgs.empty());
  for (size_t i = 0, lsize = linProgs.size(); i < lsize; i++)
  {
    Expr p = linProgs[i].first;
    d_progDefs.emplace_back(p);
    d_progToDef[p] = linProgs[i].second;
  }
}

void LeanMetaReduce::finalizePrograms()
{
  std::set<Expr> progProcessed;
  std::vector<Expr> waiting;
  std::set<Expr> waitingDef;
  for (size_t i = 0, nprogs = d_progDefs.size(); i < nprogs; i++)
  {
    Expr prog = d_progDefs[i];
    bool isDefine = (d_progIsDefine.find(prog) != d_progIsDefine.end());
    Expr def = d_progToDef[prog];
    finalizeProgram(prog, def, isDefine);
/*
    // Trying to minimize mutual blocks....
    Expr prog = d_progDefs[i];
    if (progProcessed.find(prog) != progProcessed.end())
    {
      continue;
    }
    Expr def = d_progToDef[prog];
    std::vector<Expr> calls =
        StdPlugin::getSubtermsKind(Kind::PROGRAM_CONST, def);
    bool hasWaitingDef = false;
    for (size_t j = 0, ncalls = calls.size(); j < ncalls; j++)
    {
      Expr sc = calls[j];
      if (sc != prog && progProcessed.find(sc) == progProcessed.end()
          && d_progToDef.find(sc) != d_progToDef.end())
      {
        if (std::find(waiting.begin(), waiting.end(), sc) == waiting.end())
        {
          waitingDef.insert(sc);
        }
        hasWaitingDef = true;
      }
    }
    if (!hasWaitingDef)
    {
      // go ahead and define it
      bool isDefine = (d_progIsDefine.find(prog) != d_progIsDefine.end());
      finalizeProgram(prog, def, isDefine);
      progProcessed.insert(prog);
    }
    else
    {
      // otherwise we are waiting
      waiting.push_back(prog);
    }
    // remove from waiting defs
    waitingDef.erase(prog);
    if (!waiting.empty() && waitingDef.empty())
    {
      if (waiting.size() > 1)
      {
        d_defs << "mutual" << std::endl;
      }
      for (size_t j = 0, ncalls = waiting.size(); j < ncalls; j++)
      {
        Expr prog = waiting[j];
        Expr def = d_progToDef[prog];
        if (!def.isNull())
        {
          bool isDefine = (d_progIsDefine.find(prog) != d_progIsDefine.end());
          finalizeProgram(prog, def, isDefine);
          progProcessed.insert(prog);
        }
      }
      if (waiting.size() > 1)
      {
        d_defs << "end" << std::endl;
      }
      waiting.clear();
    }
*/
  }
  Assert(waiting.empty());
}

void LeanMetaReduce::finalizeProgram(const Expr& v,
                                     const Expr& prog,
                                     bool isDefine)
{
  std::string vname = getName(v);
  Expr vt = v.getType();
  if (prog.getKind() != Kind::PROGRAM)
  {
    MetaKind vctx = getTypeMetaKind(vt);
    std::ostream* out = &d_smtDefs;
    if (vctx == MetaKind::EUNOIA)
    {
      out = &d_defs;
      (*out) << "partial ";
    }
    (*out) << "def " << cleanId(vname) << " : ";
    printMetaType(vt, *out, vctx);
    (*out) << " := ";
    printEmbTerm(prog, *out);
    (*out) << std::endl;
    return;
  }
  Expr vprog = prog;
  size_t ncases = vprog.getNumChildren();
  Trace("lean-meta") << "*** Setting up program " << v << " / "
                     << !prog.isNull() << std::endl;
  // (*out) << "/- " << (prog.isNull() ? "fwd-decl: " : "program: ") << v
  //        << " -/" << std::endl;
  std::stringstream decl;
  std::vector<MetaKind> vctxArgs;
  size_t nargs = vt.getNumChildren();
  // determine which output stream to print on
  bool isCheckerDef = false;
  for (size_t j = 0; j < nargs; j++)
  {
    vctxArgs.push_back(getTypeMetaKind(vt[j]));
    isCheckerDef |= isCheckerMetaKind(vctxArgs.back());
  }
  std::ostream* out = nullptr;
  MetaKind tmk = MetaKind::EUNOIA;
  if (isCheckerDef)
  {
    out = &d_eoChecker;
  }
  else if (isSmtMetaKind(vctxArgs.back()))
  {
    out = &d_smtDefs;
    tmk = MetaKind::SMT_TYPE;
  }
  else
  {
    out = &d_defs;
    // FIXME
    decl << "partial ";
  }
  // $eo_model is used only for VC generation
  if (vname.compare(0, 9, "$eo_model") == 0)
  {
    return;
  }
  // exception: conversion from Eunoia to SMT is printed on defs
  if (vname.compare(0, 10, "$eo_to_smt") == 0)
  {
    out = &d_eoIsObjDefs;
  }
  else if (vname.compare(0, 8, "$eo_lem_") == 0)
  {
    out = &d_lemmaAuxDef;
  }
  if (vname == "$smtx_model_eval")
  {
    decl << "noncomputable ";
    out = &d_smt;
  }
  decl << "def " << cleanId(vname);
  size_t macroStartArg = 1;
  bool macroSuccess = true;
  while (macroSuccess && macroStartArg < vt.getNumChildren())
  {
    Trace("lean-meta") << "...check if argument " << macroStartArg
                       << " is macro" << std::endl;
    if (vctxArgs[macroStartArg - 1] == MetaKind::EUNOIA)
    {
      macroSuccess = false;
      break;
    }
    Expr v;
    for (size_t i = 0; i < ncases; i++)
    {
      Expr vn = vprog[i][0][macroStartArg];
      if ((v.isNull() && vn.getKind() == Kind::PARAM) || v == vn)
      {
        v = vn;
        continue;
      }
      macroSuccess = false;
      break;
    }
    if (macroSuccess)
    {
      decl << " (" << v << " : ";
      printMetaType(vt[macroStartArg - 1], decl, tmk);
      decl << ")";
      macroStartArg++;
    }
  }
  // whether we should do an ITE output instead of a match
  // this is to speed up the Lean C compiler
  bool optIte = false;  // (ncases>=10 && macroStartArg+1==nargs);
  // bool optIte = false;
  if (optIte)
  {
    decl << "(__input : ";
    printMetaType(vt[macroStartArg - 1], decl, tmk);
    decl << ")";
  }
  // Trace("lean-meta") << "Type is " << vt << std::endl;
  decl << " : ";
  Assert(vt.getKind() == Kind::PROGRAM_TYPE)
      << "bad type " << vt << " for " << v;
  Assert(nargs > 1);
  size_t typeStart = macroStartArg + (optIte ? 1 : 0);
  for (size_t i = typeStart; i < nargs; i++)
  {
    Trace("lean-meta") << "Print meta type " << vt[i - 1] << std::endl;
    printMetaType(vt[i - 1], decl, tmk);
    decl << " -> ";
  }
  std::stringstream retType;
  printMetaType(vt[nargs - 1], retType, tmk);
  decl << retType.str();
  // Trace("lean-meta") << "DECLARE " << decl.str() << std::endl;
  Trace("lean-meta") << "*** FINALIZE " << v << std::endl;
  if (!optIte && macroStartArg == vt.getNumChildren())
  {
    // no cases necessary, just a macro
    Assert(vprog.getNumChildren() == 1);
    decl << " :=" << std::endl;
    decl << "  ";
    printEmbTerm(vprog[0][1], decl, tmk);
    (*out) << decl.str() << std::endl << std::endl;
    return;
  }
  decl << (optIte ? " :=" : "") << std::endl;
  // compile the pattern matching
  std::stringstream cases;
  if (optIte)
  {
    cases << "  ";
  }
  // If the return type does not have meta-kind Eunoia, then it cannot get
  // stuck. We ensure that all programs over such types are total.
  // We also are not a Eunoia program if we called this method via a define
  // command.
  MetaKind retk = getTypeMetaKind(vt[nargs - 1]);
  // determine if we should guard this program with stuck cases
  // we do not check for stuck for define, since it is a macro in Eunoia
  // and hence always reduces.
  // we do not check for stuck in checker definitions since we manually know
  // that such checks are spurious.
  if (retk == MetaKind::EUNOIA && !isDefine && !isCheckerDef)
  {
    for (size_t i = macroStartArg; i < nargs; i++)
    {
      if (vctxArgs[i - 1] != MetaKind::EUNOIA)
      {
        continue;
      }
      // optimization: check if we only match against non-parameter terms.
      // in this case, there is no need to check stuckness
      bool matchesParam = false;
      for (size_t j = 0; j < ncases; j++)
      {
        if (vprog[j][0][i].getKind() == Kind::PARAM)
        {
          matchesParam = true;
          break;
        }
      }
      if (!matchesParam)
      {
        continue;
      }
      Assert(i >= macroStartArg);
      if (optIte)
      {
        cases << "if let Term.Stuck := __input then Term.Stuck" << std::endl;
        cases << "  else ";
        continue;
      }
      cases << "  | ";
      for (size_t j = macroStartArg; j < nargs; j++)
      {
        if (j > macroStartArg)
        {
          cases << ", ";
        }
        if (i == j)
        {
          cases << "Term.Stuck ";
        }
        else
        {
          cases << "_ ";
        }
      }
      cases << " => Term.Stuck" << std::endl;
    }
  }
  bool wasDefault = false;
  for (size_t i = 0; i < ncases; i++)
  {
    const Expr& c = vprog[i];
    const Expr& hd = c[0];
    const Expr& body = c[1];
    std::stringstream currCase;
    Assert(hd.getNumChildren() == nargs);
    wasDefault = true;
    std::stringstream patMatch;
    for (size_t j = macroStartArg, nhdchild = hd.getNumChildren(); j < nhdchild;
         j++)
    {
      if (j > macroStartArg)
      {
        patMatch << ", ";
      }
      // Print the pattern matching predicate for this argument, all
      // concatenated together.
      // Initial context depends on the kind of the argument type of the
      // program.
      printEmbTerm(hd[j], patMatch, tmk, false);
      // note this further assumes variables are unique as they are required
      // to be unique at this point
      if (hd[j].getKind() != Kind::PARAM)
      {
        wasDefault = false;
      }
    }
    std::stringstream ssret;
    printEmbTerm(body, ssret, tmk);
    if (optIte)
    {
      if (wasDefault)
      {
        cases << "let " << patMatch.str() << " := __input; " << ssret.str()
              << std::endl;
      }
      else
      {
        cases << "if let " << patMatch.str() << " := __input then "
              << ssret.str() << std::endl;
        cases << "  else ";
      }
    }
    else
    {
      cases << "  | " << patMatch.str() << " => " << ssret.str() << std::endl;
    }
  }
  if (!wasDefault)
  {
    if (optIte)
    {
      cases << retType.str() << ".Stuck" << std::endl;
    }
    // should be a datatype with stuck
    // checker definitions we ensure are total
    else if (!isCheckerDef
             && (retk == MetaKind::EUNOIA || retk == MetaKind::PROOF))
    {
      cases << "  | ";
      for (size_t j = macroStartArg; j < nargs; j++)
      {
        if (j > macroStartArg)
        {
          cases << ", ";
        }
        cases << "_";
      }
      cases << " => " << retType.str() << ".Stuck" << std::endl;
    }
  }
  // axiom
  (*out) << decl.str();
  (*out) << cases.str();
  (*out) << std::endl;
  (*out) << std::endl;
  // if it corresponds to a proof rule, print a Lean theorem
}

void LeanMetaReduce::define(const std::string& name, const Expr& e)
{
  // NOTE: the code here ensures that we preserve definitions for the final vc.
  // This is required since we do not replace e.g. eo::list_concat with
  // $eo_list_concat until the final generation of smt2. This means that this
  // definition (although it would have been inlined) is still necessary to
  // define what eo::list_concat will desugar to. Also note this definition is
  // properly preserved by trim_defs which is agnostic to eo:: vs $eo_.
  if (name.compare(0, 4, "$eo_") != 0)
  {
    return;
  }

  Expr tmp;
  Expr prog;
  if (buildLambdaDefineProgram(name, e, tmp, prog))
  {
    Trace("lean-meta") << "Look at define " << name << std::endl;
    Trace("lean-meta") << "...do program " << tmp << " / " << prog
                       << " instead" << std::endl;
    d_progDefs.emplace_back(tmp);
    d_progToDef[tmp] = prog;
    d_progIsDefine.insert(tmp);
    Trace("lean-meta") << "...finished lambda program" << std::endl;
  }
  else
  {
    Expr tmp = d_state.mkSymbol(Kind::PROGRAM_CONST, name, d_state.mkAny());
    d_progDefs.emplace_back(tmp);
    d_progToDef[tmp] = e;
  }
}

void LeanMetaReduce::finalizeDecl(const Expr& e)
{
  if (!beginFinalizeDecl(e))
  {
    return;
  }
  // first, determine which datatype (if any) this belongs to
  std::stringstream ss;
  ss << e;
  std::string sname = ss.str();
  std::stringstream* out = nullptr;
  // get the meta-kind based on its name
  std::string cnamek;
  MetaKind tk = getMetaKind(d_state, e, cnamek);
  std::string cname = cleanSmtId(cnamek);
  if (tk == MetaKind::EUNOIA)
  {
    out = &d_embedTermDt;
  }
  else if (tk == MetaKind::SMT)
  {
    out = &d_smtDt;
  }
  else if (tk == MetaKind::SMT_TYPE)
  {
    out = &d_smtTypeDt;
  }
  else if (tk == MetaKind::SMT_VALUE)
  {
    out = &d_smtValueDt;
  }
  else if (tk == MetaKind::CHECKER_RULE)
  {
    out = &d_ruleDt;
  }
  else if (tk == MetaKind::CHECKER_CMD)
  {
    out = &d_cmdDt;
  }
  if (out == nullptr)
  {
    Trace("lean-meta") << "Do not include " << e << std::endl;
    return;
  }
  Trace("lean-meta") << "Include " << e << std::endl;
  //(*out) << "  /- " << (isEmbedCons(e) ? "smt-cons: " : "user-decl: ") <<
  // cnamek
  //       << " -/" << std::endl;
  Expr c = e;
  Expr ct = d_tc.getType(c);
  // (*out) << "  ; type is " << ct << std::endl;
  Attr attr = d_state.getConstructorKind(e.getValue());
  // (*out) << "  ; attr is " << attr << std::endl;
  (*out) << "  | ";
  (*out) << cname << " : ";
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
  // revert overloads
  if (cnamek.compare(0, 5, "$eoo_") == 0)
  {
    size_t firstDot = cnamek.find('.');
    Assert(firstDot != std::string::npos && firstDot > 5);
    cnamek = cnamek.substr(5, firstDot - 5);
  }
  for (size_t i = 0; i < nopqArgs; i++)
  {
    // print its type using the utility,
    // which takes into account what the type is in the final embedding
    Expr typ = ct[i];
    if (ct[i].getKind() == Kind::QUOTE_TYPE)
    {
      Expr targ = ct[i][0];
      typ = d_tc.getType(targ);
    }
    std::stringstream sst;
    if (!printMetaType(typ, sst, tk))
    {
      // TODO: never happens?
      sst << "Term";
    }
    (*out) << sst.str() << " -> ";
    //(*out) << "; Printing datatype argument type " << typ << " gives \"" <<
    // sst.str() << "\" " << termKindToString(tk) << std::endl;
  }
  printMetaTypeKind(tk, *out);
  (*out) << std::endl;
}

void LeanMetaReduce::finalizeChecker()
{
  const std::string outPath = emitResourceFile(
      "plugins/lean_meta/lean_meta_checker.lean",
      "plugins/lean_meta/lean_meta_checker_gen.lean",
      {{"$LEAN_DEFS$", d_defs.str()},
       {"$LEAN_TERM_DEF$", d_embedTermDt.str()},
       {"$LEAN_CHECKER_RULE_DEF$", d_ruleDt.str()},
       {"$LEAN_CHECKER_CMD_DEF$", d_cmdDt.str()},
       {"$LEAN_CHECKER_DEFS$", d_eoChecker.str()}});
  Trace("lean-meta") << "Write lean-defs " << outPath << std::endl;
}

void LeanMetaReduce::finalizeSmtModel()
{
  const std::string outPath = emitResourceFile(
      "plugins/lean_meta/lean_meta_smt_model.lean",
      "plugins/lean_meta/lean_meta_smt_model_gen.lean",
      {{"$LEAN_SMT_TYPE_DEF$", d_smtTypeDt.str()},
       {"$LEAN_SMT_TERM_DEF$", d_smtDt.str()},
       {"$LEAN_SMT_VALUE_DEF$", d_smtValueDt.str()},
       {"$LEAN_SMT_EVAL_DEFS$", d_smtDefs.str()},
       {"$LEAN_SMT_EVAL$", d_smt.str()}});
  Trace("lean-meta") << "Write lean-defs " << outPath << std::endl;
}

void LeanMetaReduce::finalizeSpec()
{
  const std::string outPath = emitResourceFile(
      "plugins/lean_meta/lean_meta_spec.lean",
      "plugins/lean_meta/lean_meta_spec_gen.lean",
      {{"$LEAN_EO_IS_OBJ_DEFS$", d_eoIsObjDefs.str()},
       {"$LEAN_EO_IS_OBJ$", d_eoIsObj.str()},
       {"$LEAN_EO_IS_REFUTATION_DEF$", d_eoIsRef.str()}});
  Trace("lean-meta") << "Write lean-defs " << outPath << std::endl;
}

void LeanMetaReduce::finalizeLemmas()
{
  const std::string outPath = emitResourceFile(
      "plugins/lean_meta/lean_meta_lemmas.lean",
      "plugins/lean_meta/lean_meta_lemmas_gen.lean",
      {{"$LEAN_THMS$", d_thms.str()},
       {"$LEAN_LEMMA_AUX_DEFS$", d_lemmaAuxDef.str()}});
  Trace("lean-meta") << "Write lean-defs " << outPath << std::endl;
}

void LeanMetaReduce::finalize()
{
  finalizePrograms();
  // is obj is trivial, call the method
  d_eoIsObj << "  | intro (x : Term) : eo_is_obj x (__eo_to_smt x)"
            << std::endl;
  // refutation is if the method returns true
  d_eoIsRef << "  | intro (F : Term) (c : CCmdList) : " << std::endl;
  d_eoIsRef << "    (__eo_checker_is_refutation F c) = true -> "
               "(eo_is_refutation F c)"
            << std::endl;

  if (d_ruleDt.str().empty())
  {
    d_ruleDt << "  | none : CRule" << std::endl;
  }
  // versions that split
  finalizeChecker();
  finalizeSmtModel();
  finalizeSpec();
  finalizeLemmas();
}

bool LeanMetaReduce::echo(const std::string& msg)
{
  std::cout << "ECHO " << msg << std::endl;
  if (msg.compare(0, 10, "lean-meta ") == 0)
  {
    std::string eosc = msg.substr(10);
    size_t pos = eosc.find(' ');
    if (pos != std::string::npos)
    {
      eosc.erase(pos);  // erase from the space to the end
    }
    Expr vv = d_state.getVar(eosc);
    if (vv.isNull())
    {
      Assert(false) << "When making Lean theorem, could not find program "
                    << eosc;
    }
    d_thms << "/- correctness theorem for " << cleanId(eosc) << " -/"
           << std::endl;
    std::stringstream call;
    ConjectureType ctype = StdPlugin::optionSmtMetaConjectureType();
    if (ctype == ConjectureType::VC)
    {
      d_thms << "theorem correct_" << cleanId(eosc) << " (M : SmtModel) ";
      Expr def = d_state.getProgram(vv.getValue());
      Expr vt = vv.getType();
      std::stringstream pcs;
      if (vt.getKind() == Kind::PROGRAM_TYPE)
      {
        d_thms << "(";
        std::stringstream conds;
        std::stringstream progArgs;
        for (size_t i = 1; i < vt.getNumChildren(); i++)
        {
          d_thms << (i > 1 ? " " : "") << "x" << i;
          if (getTypeMetaKind(vt[i - 1]) == MetaKind::PROOF)
          {
            conds << "  (eo_interprets M x" << i << " true) ->" << std::endl;
            progArgs << (i > 1 ? " " : "") << "(Proof.pf x" << i << ")";
          }
          else
          {
            progArgs << (i > 1 ? " " : "") << "x" << i;
          }
        }
        d_thms << " : Term)"
               << " :" << std::endl;
        d_thms << conds.str();
        pcs << "(" << cleanId(eosc) << " " << progArgs.str() << ")";
      }
      else
      {
        d_thms << ":" << std::endl;
        pcs << cleanId(eosc);
      }
      d_thms << "  (Not (" << pcs.str() << " = Term.Stuck)) ->" << std::endl;
      d_thms << "  (eo_interprets M ";
      d_thms << pcs.str() << " true) :=" << std::endl;
      d_thms << "by" << std::endl;
      d_thms << "  sorry" << std::endl;
      d_thms << std::endl;
    }
    else
    {
      Assert(false) << "Unknown conjecture type";
    }
    return false;
  }
  return true;
}

bool LeanMetaReduce::isProgram(const Expr& t)
{
  return (t.getKind() == Kind::PROGRAM_CONST);
}

MetaKind LeanMetaReduce::getTypeMetaKind(const Expr& typ) const
{
  return getTypeMetaKindFor(typ, MetaKind::EUNOIA, false);
}

MetaKind LeanMetaReduce::getMetaKind(State&,
                                     const Expr& e,
                                     std::string& cname) const
{
  return getMetaKindFor(e, cname);
}

std::string LeanMetaReduce::cleanSmtId(const std::string& id)
{
  if (id == "repeat")
  {
    return "__smt_" + id;
  }
  if (id == "end" || id == "variable")
  {
    return "__eo_" + id;
  }
  std::string idc = id;
  idc = replace_all(idc, "++", "concat");
  idc = replace_all(idc, "+", "plus");
  idc = replace_all(idc, "-", "neg");
  idc = replace_all(idc, "*", "mult");
  idc = replace_all(idc, "=>", "imp");
  idc = replace_all(idc, "<=", "leq");
  idc = replace_all(idc, "<", "lt");
  idc = replace_all(idc, ">=", "geq");
  idc = replace_all(idc, ">", "gt");
  idc = replace_all(idc, "=", "eq");
  idc = replace_all(idc, "/", "qdiv");
  idc = replace_all(idc, "^", "exp");
  idc = replace_all(idc, ".", "_");
  idc = replace_all(idc, "@", "_at_");
  idc = replace_all(idc, "$", "__");
  return idc;
}

std::string LeanMetaReduce::cleanId(const std::string& id)
{
  std::string idc = id;
  idc = replace_all(idc, "-", "_");
  return cleanSmtId(idc);
}

}  // namespace ethos
