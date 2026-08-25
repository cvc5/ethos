/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "lean_meta_reduce.h"

#include <cctype>
#include <fstream>
#include <sstream>
#include <string>

#include "../linear_patterns/linear_patterns.h"
#include "state.h"

#define INFER_TOTAL_DEFS

namespace ethos {

namespace {

/** Whether to collapse atomic theory operators into SmtTheoryOp. */
bool optionSmtTheoryOp() { return false; }

/** Whether to collapse atomic user operators into UserOp. */
bool optionEoUserOp() { return true; }

}  // namespace

LeanMetaReduce::LeanMetaReduce(State& s,
                               bool generateParser,
                               const std::string& configFile)
    : MetaReducePlugin(s), d_generateParser(generateParser)
{
  d_typeToMetaKind["$eo_Term"] = MetaKind::EUNOIA;
  d_typeToMetaKind["$eo_Proof"] = MetaKind::PROOF;
  d_typeToMetaKind["$eo_Rule"] = MetaKind::CHECKER_RULE;
  d_typeToMetaKind["$eo_Cmd"] = MetaKind::CHECKER_CMD;
  d_prefixToMetaKind["r"] = MetaKind::CHECKER_RULE;
  d_prefixToMetaKind["cmd"] = MetaKind::CHECKER_CMD;
#ifdef INFER_TOTAL_DEFS
  d_hasDefs = false;
  d_defsTotal << "mutual" << std::endl << std::endl;
#endif
  if (optionSmtTheoryOp())
  {
    d_smtDt << "  | TheoryOp : SmtTheoryOp -> SmtTerm" << std::endl;
  }
  // NOTE: any partial def can be forced by adding the method names to
  // d_partialExc, e.g. d_partialExc.insert("$str_re_consume_rec");

  // Why a generated definition terminates is Lean text rather than anything
  // this plugin derives, so it is stated in a file of its own. The one of the
  // deep embedding holds for every input; the one of the input signature is
  // named on the command line, and an input whose programs all recurse
  // structurally needs none.
  readTerminationClauses(getResourcePath("plugins/lean_meta/termination.lean"));
  if (!configFile.empty())
  {
    readTerminationClauses(configFile);
  }
}

void LeanMetaReduce::readTerminationClauses(const std::string& path)
{
  std::ifstream in(path);
  if (!in.is_open())
  {
    EO_FATAL() << "LeanMetaReduce: could not read the termination clauses at "
               << path;
  }
  // the programs the block being read is of, and the text of the clause
  std::vector<std::string> names;
  std::stringstream body;
  // A block ends where the next one begins, so what has been read is taken
  // once the whole of it is known, here and again at the end of the file.
  auto take = [&]() {
    std::string text = body.str();
    size_t e = text.find_last_not_of(" \t\n");
    text = (e == std::string::npos ? "" : text.substr(0, e + 1));
    if (!text.empty())
    {
      for (const std::string& n : names)
      {
        d_terminatingBy[n] = text;
      }
    }
    names.clear();
    body.str("");
  };
  std::string line;
  while (std::getline(in, line))
  {
    // A clause is Lean text and holds no comment of its own, so a comment
    // line ends the block being read, whether it opens the next one by naming
    // what its clause is of or is prose written between the two.
    if (line.compare(0, 2, "--") == 0)
    {
      take();
      if (line.compare(0, 4, "-- $") == 0)
      {
        std::stringstream ls(line.substr(3));
        std::string name;
        while (ls >> name)
        {
          names.push_back(name);
        }
      }
      continue;
    }
    if (!names.empty())
    {
      body << line << std::endl;
    }
  }
  take();
}

LeanMetaReduce::~LeanMetaReduce() {}

bool LeanMetaReduce::isBuiltinMetaSymbol(const std::string& sname) const
{
  return sname.compare(0, 5, "$smt_") == 0
         || sname.compare(0, 8, "$native_") == 0
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
  if (isEmbedMetaKind(tk))
  {
    os << getEmbedTypeName(getEmbedTypeApp(t));
    return true;
  }
  return printMetaTypeKind(tk, os);
}

bool LeanMetaReduce::printMetaTypeKind(MetaKind k, std::ostream& os) const
{
  switch (k)
  {
    case MetaKind::EUNOIA: os << "Term"; break;
    case MetaKind::SMT_TYPE: os << "SmtType"; break;
    case MetaKind::SMT: os << "SmtTerm"; break;
    case MetaKind::SMT_VALUE: os << "SmtValue"; break;
    case MetaKind::SMT_MAP: os << "SmtMap"; break;
    case MetaKind::SMT_SEQ: os << "SmtSeq"; break;
    case MetaKind::PROOF: os << "Proof"; break;
    case MetaKind::CHECKER_RULE: os << "CRule"; break;
    case MetaKind::CHECKER_CMD: os << "CCmd"; break;
    default: return false;
  }
  return true;
}

bool LeanMetaReduce::isAtomicSmt(const Expr& c, const std::string& cname)
{
  if (!optionSmtTheoryOp())
  {
    return false;
  }
  Attr attr = d_state.getAttributeKind(c.getValue());
  if (attr != Attr::OPAQUE)
  {
    if (cname == "None")
    {
      return false;
    }
    return true;
  }
  return false;
}

bool LeanMetaReduce::isAtomicEo(const Expr& c, const std::string& cname, size_t& arity)
{
  if (!optionEoUserOp())
  {
    return false;
  }
  Attr attr = d_state.getAttributeKind(c.getValue());
  std::string rawName = getName(c);
  if (rawName.compare(0, 4, "$emb") == 0)
  {
    return false;
  }
  if (attr != Attr::OPAQUE)
  {
    if (cname == "Stuck" || cname == "Type" || cname == "FunType"
        || cname == "Bool" || cname.compare(0, 4, "$eo_") == 0)
    {
      return false;
    }
    arity = 0;
    return true;
  }
  Expr ct = c.getType();
  Assert (ct.getKind()==Kind::FUNCTION_TYPE);
  arity = ct.getNumChildren() - 1;
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
      bool needsCparen = false;
      size_t uarity;
      if (k == MetaKind::SMT && isAtomicSmt(c, cname))
      {
        needsCparen = true;
        os << "(SmtTerm.TheoryOp SmtTheoryOp";
      }
      else if (k == MetaKind::EUNOIA && isAtomicEo(c, cname, uarity))
      {
        if (uarity==0)
        {
          needsCparen = true;
          os << "(Term.UOp UserOp";
        }
        else
        {
          os << "Term.UOp" << uarity << " UserOp" << uarity;
        }
      }
      else if (isEmbedMetaKind(k))
      {
        // a constructor of a datatype declared via $native_embed_*; its
        // datatype name is carried by its return type
        os << getEmbedTypeName(getEmbedTypeApp(c.getType()));
      }
      else if (!printMetaTypeKind(k, os))
      {
        os << "Term";
      }
      os << "." << cleanSmtId(cname);
      if (needsCparen)
      {
        os << ")";
      }
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
        os << "(-" << cin.toString() << " : native_Int)";
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
      os << "(native_mk_rational " << rstr << ")";
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
      os << "(Term.String ";
      std::string css = l->toString();
      AlwaysAssert(css.find_first_of("\"\\") == std::string::npos)
          << "Lean meta only supports printable ASCII string literals without "
             "quotes or backslashes, got "
          << l->d_str;
      if (css.empty())
      {
        // empty string
        os << "[]";
      }
      else
      {
        // native literals
        os << "(native_string_lit \"" << css << "\")";
      }
      os << ")";
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
  AlwaysAssert(oApp.getKind() == Kind::APPLY_OPAQUE)
      << "Bad kind for opaque " << oApp.getKind() << " " << oApp;
  AlwaysAssert(isSmtApplyApp(oApp))
      << "Expected smt apply app when asking for embed name " << oApp;
  const Literal* l = oApp[1].getValue()->asLiteral();
  AlwaysAssert(l != nullptr)
      << "Expected string literal in smt apply app " << oApp;
  std::string smtStr = l->d_str.toString();
  // literals don't need native_
  if (is_integer(smtStr) || smtStr == "true" || smtStr == "false")
  {
    return smtStr;
  }
  if (!smtStr.empty() && smtStr.compare(0, 1, "\"") == 0)
  {
    AlwaysAssert(smtStr.size() >= 2 && smtStr.back() == '"'
                 && smtStr.find('\\') == std::string::npos
                 && smtStr.find('"', 1) == smtStr.size() - 1)
        << "Lean meta only supports quoted native strings with printable ASCII "
           "bodies that contain no quotes or backslashes, got "
        << l->d_str;
    if (smtStr.length()==2)
    {
      // empty string
      return "[]";
    }
    // native literals
    std::stringstream ss;
    ss << "(native_string_lit " << smtStr << ")";
    return ss.str();
  }
  else if (smtStr.compare(0, 6, "UserOp")==0)
  {
    return smtStr;
  }
  std::stringstream ss;
  ss << "native_" << cleanSmtId(smtStr);
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
      // if its just an $native_apply_0, don't print
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
    else if (recTerm.getNumChildren() == 0)
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
      // `($native_apply_3 "ite"` becomes `(ite`
      if (sname.compare(0, 14, "$native_apply_") == 0
          || sname.compare(0, 13, "$native_type_") == 0
          || sname.compare(0, 16, "$native_datatype") == 0)
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
          // this handles the corner case that ($native_apply_0 "true") should
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
      os << "(Term.Var ";
      cparen[key]++;
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
              bool isDefine = (d_progIsDefine.find(prog) !=
       d_progIsDefine.end()); finalizeProgram(prog, def, isDefine);
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
  if (vname == "$eo_ite")
  {
    return;
  }
  Expr vt = v.getType();
  if (prog.getKind() != Kind::PROGRAM)
  {
    MetaKind vctx = getTypeMetaKind(vt);
    std::ostream* out = &d_smtDefs;
    if (vctx == MetaKind::EUNOIA)
    {
#ifdef INFER_TOTAL_DEFS
      out = &d_defsTotal;
      // define is only used for very rare cases of $eo_, and for
      // (argument+premise)-less proof rules, which we assume are terminating.
#else
      out = &d_defs;
      (*out) << "partial ";
#endif
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
    out = &d_defsTotal;
  }
  bool isSimple = true;
  bool needsPartial = false;
  // check if trivially not recursive?
  std::vector<Expr> prets;
  for (size_t i = 0, nchildren = prog.getNumChildren(); i < nchildren; i++)
  {
    prets.push_back(prog[i][1]);
  }
  Expr allRets = d_state.mkExpr(Kind::TUPLE, prets);
  std::vector<Expr> calls =
      StdPlugin::getSubtermsKind(Kind::PROGRAM_CONST, allRets);
  for (const Expr& e : calls)
  {
    // if there is any (mutual) recursion, or reference to a non-total
    // function, set needsPartial to true.
    if (d_partialDefProgs.find(e) != d_partialDefProgs.end())
    {
      needsPartial = true;
      isSimple = false;
      break;
    }
    if (e != v && d_simpleDefProgs.find(e) == d_simpleDefProgs.end())
    {
      isSimple = false;
    }
  }
  std::string rawName = vname;
  if (vname.compare(0, 6, "$eo.l.") == 0)
  {
    const size_t namePos = vname.find('.', 6);
    AlwaysAssert(namePos != std::string::npos && namePos + 1 < vname.size())
        << "Malformed linear-pattern program name " << vname;
    rawName = vname.substr(namePos + 1);
  }
  if (d_partialExc.find(rawName)!=d_partialExc.end())
  {
    needsPartial = true;
  }
  // insist that builtin eo:: operators are all total.
  if (vname.compare(0, 4, "$eo_") == 0
    && vname.compare(0, 9, "$eo_prog_") != 0)
  {
    needsPartial = false;
  }
#ifndef INFER_TOTAL_DEFS
  // FIXME
  needsPartial = true;
#endif
  if (isSimple)
  {
    d_simpleDefProgs.insert(v);
  }
  if (needsPartial)
  {
    if (!d_hasDefs)
    {
      d_hasDefs = true;
      d_defs << "mutual" << std::endl << std::endl;
    }
    out = &d_defs;
    decl << "partial ";
    d_partialDefProgs.insert(v);
  }
  else
  {
    d_totalDefProgs.insert(v);
  }

  // $eo_model is used only for VC generation
  if (vname.compare(0, 9, "$eo_model") == 0)
  {
    return;
  }
  // exception: conversion from Eunoia to SMT is printed on defs
  if (vname.compare(0, 10, "$eo_to_smt") == 0)
  {
    out = isSimple ? &d_eoIsObjDefsSimple : &d_eoIsObjDefs;
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
  (*out) << decl.str();
  (*out) << cases.str();
  std::map<std::string, std::string>::iterator ittb = d_terminatingBy.find(vname);
  if (ittb!=d_terminatingBy.end())
  {
    (*out) << ittb->second << std::endl;
  }
  (*out) << std::endl;
  (*out) << std::endl;
}

void LeanMetaReduce::define(const std::string& name, const Expr& e)
{
  if (isParseDefName(name))
  {
    // A definition preserved by the desugar stage only so that the identifier
    // it introduces can be resolved when parsing a proof. It contributes to the
    // generated parser and to nothing else, see finalizeParseDefs.
    d_parseDefs.emplace_back(getParseDefSurfaceName(name), e);
    return;
  }
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
  // definitions of $native_embed_* types only carry the name of the embedded
  // datatype for classification; they do not induce a definition
  if (!getEmbedTypeApp(e).isNull())
  {
    return;
  }

  Expr tmp;
  Expr prog;
  if (buildLambdaDefineProgram(name, e, tmp, prog))
  {
    Trace("lean-meta") << "Look at define " << name << std::endl;
    Trace("lean-meta") << "...do program " << tmp << " / " << prog << " instead"
                       << std::endl;
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
  if (sname == "$eo_pf")
  {
    return;
  }
  std::stringstream* out = nullptr;
  // get the meta-kind based on its name
  std::string cnamek;
  MetaKind tk = getMetaKind(d_state, e, cnamek);
  // `$eoo_` names carry the overload identity. Keep them mangled so distinct
  // operators such as unary and binary `-` remain distinct Lean constructors.
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
    d_emittedRules.insert(cname);
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
  Attr attr = d_state.getAttributeKind(e.getValue());
  // (*out) << "  ; attr is " << attr << std::endl;
  size_t nopqArgs = 0;
  Expr retType = ct;
  if (attr == Attr::OPAQUE)
  {
    // opaque symbols are non-nullary constructors
    Assert(ct.getKind() == Kind::FUNCTION_TYPE);
    nopqArgs = ct.getNumChildren() - 1;
    retType = ct[nopqArgs];
  }
  size_t uarity;
  if (tk == MetaKind::SMT && isAtomicSmt(c, cnamek))
  {
    d_smtTOpDt << "  | " << cname << " : SmtTheoryOp" << std::endl;
    return;
  }
  else if (tk == MetaKind::EUNOIA && isAtomicEo(c, cnamek, uarity))
  {
    AlwaysAssert(uarity < 4)
        << "Lean meta supports at most three opaque operator indices, got "
        << uarity << " for " << e;
    d_emittedUserOps.insert(std::make_pair(cname, uarity));
    std::stringstream& etd = d_embedTOpDt[uarity];
    etd << "  | " << cname << " : UserOp";
    if (uarity>0)
    {
      etd << uarity;
    }
    etd << std::endl;
    return;
  }
  (*out) << "  | " << cname << " : ";
  AlwaysAssert(attr != Attr::AMB && attr != Attr::AMB_DATATYPE_CONSTRUCTOR);
  std::vector<std::string> argTypes;
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
    argTypes.push_back(sst.str());
    (*out) << sst.str() << " -> ";
    //(*out) << "; Printing datatype argument type " << typ << " gives \"" <<
    // sst.str() << "\" " << termKindToString(tk) << std::endl;
  }
  printMetaTypeKind(tk, *out);
  (*out) << std::endl;
  // the ordering key methods are generated in lockstep with the datatypes they
  // order, so that the tag of a constructor is its index in the datatype.
  if (tk == MetaKind::SMT_TYPE)
  {
    printOrderKeyCase(cname, argTypes, d_smtTypeNcons, d_smtTypeKey);
    d_smtTypeNcons++;
  }
  else if (tk == MetaKind::SMT_VALUE)
  {
    printOrderKeyCase(cname, argTypes, d_smtValueNcons, d_smtValueKey);
    d_smtValueNcons++;
  }
}

std::string LeanMetaReduce::getOrderKeyMethod(const std::string& t)
{
  // By convention, the key method for a type is named after the type: drop the
  // Smt or native_ prefix, lowercase the first letter and append Key, e.g.
  // SmtDatatypeDecl is ordered by datatypeDeclKey and native_Int by intKey.
  // The methods for the types that are not generated are given by the
  // lean_meta_smt_value_order.lean template.
  std::string base;
  if (t.compare(0, 3, "Smt") == 0)
  {
    base = t.substr(3);
  }
  else if (t.compare(0, 7, "native_") == 0)
  {
    base = t.substr(7);
  }
  if (base.empty())
  {
    return std::string();
  }
  base[0] = std::tolower(static_cast<unsigned char>(base[0]));
  return base + "Key";
}

void LeanMetaReduce::printOrderKeyCase(const std::string& cname,
                                       const std::vector<std::string>& argTypes,
                                       size_t tag,
                                       std::ostream& os) const
{
  std::stringstream keys;
  for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
  {
    std::string method = getOrderKeyMethod(argTypes[i]);
    if (method.empty())
    {
      // An argument whose type does not follow the naming convention, so that
      // we cannot name its key method. This does not happen for the value and
      // type datatypes; warn rather than silently emit Lean that will not
      // compile.
      Warning() << "Lean value order: constructor " << cname
                << " has argument of type " << argTypes[i]
                << ", which does not name an ordering key method" << std::endl;
      method = "natKey";
    }
    if (i > 0)
    {
      keys << ", ";
    }
    keys << method << " x" << (i + 1);
  }
  os << "  | ." << cname;
  for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
  {
    os << " x" << (i + 1);
  }
  os << " => node " << tag << " [" << keys.str() << "]" << std::endl;
}

void LeanMetaReduce::finalizeChecker()
{  
  const std::string outPatht =
      emitResourceFile("plugins/lean_meta/lean_meta_checker_term.lean",
                       "plugins/lean_meta/lean_meta_checker_term_gen.lean",
                       {{"$LEAN_TERM_DEF$", d_embedTermDt.str()},
                        {"$LEAN_EO_THEORY_OP_DEF$", d_embedTOpDt[0].str()},
                        {"$LEAN_EO_THEORY_OP1_DEF$", d_embedTOpDt[1].str()},
                        {"$LEAN_EO_THEORY_OP2_DEF$", d_embedTOpDt[2].str()},
                        {"$LEAN_EO_THEORY_OP3_DEF$", d_embedTOpDt[3].str()}});
  Trace("lean-meta") << "Write lean-defs-term " << outPatht << std::endl;
  const std::string outPath =
      emitResourceFile("plugins/lean_meta/lean_meta_checker.lean",
                       "plugins/lean_meta/lean_meta_checker_gen.lean",
                       {{"$LEAN_DEFS$", d_defs.str()},
                        {"$LEAN_DEFS_TOTAL$", d_defsTotal.str()},
                        {"$LEAN_CHECKER_RULE_DEF$", d_ruleDt.str()},
                        {"$LEAN_CHECKER_CMD_DEF$", d_cmdDt.str()},
                        {"$LEAN_CHECKER_DEFS$", d_eoChecker.str()},
                        {"$LEAN_EO_IS_REFUTATION_DEF$", d_eoIsRef.str()}});
  Trace("lean-meta") << "Write lean-defs " << outPath << std::endl;
}

std::string LeanMetaReduce::getParserOpTerm(const std::string& surface) const
{
  for (const ParserOp& op : d_parserOps)
  {
    std::string generated = cleanSmtId(op.d_generated);
    if (op.d_surface == surface
        && d_emittedUserOps.find(std::make_pair(generated, 0))
               != d_emittedUserOps.end())
    {
      return "(Term.UOp UserOp." + generated + ")";
    }
  }
  return std::string();
}

const LeanMetaReduce::ParserOp* LeanMetaReduce::getParserOpForGenerated(
    const std::string& generated) const
{
  for (const ParserOp& op : d_parserOps)
  {
    if (op.d_generated == generated && isEmittedParserOp(op))
    {
      return &op;
    }
  }
  return nullptr;
}

void LeanMetaReduce::printParserOp(const ParserOp& op,
                                   const std::string& name,
                                   std::ostream& ops)
{
  std::string generated = cleanSmtId(op.d_generated);
  std::stringstream term;
  if (op.d_indexArity == 0)
  {
    term << "(Term.UOp UserOp." << generated << ")";
  }
  else
  {
    term << "(Term.UOp" << op.d_indexArity << " UserOp" << op.d_indexArity
         << "." << generated;
    for (size_t i = 0; i < op.d_indexArity; ++i)
    {
      term << " x" << (i + 1);
    }
    term << ")";
  }

  std::string arity;
  if (op.d_attr == "left-assoc")
  {
    arity = ".leftAssoc";
  }
  else if (op.d_attr == "right-assoc")
  {
    arity = ".rightAssoc";
  }
  else if (op.d_attr == "left-assoc-nil")
  {
    arity = ".leftAssocNil (parserNil " + term.str() + ")";
  }
  else if (op.d_attr == "right-assoc-nil")
  {
    arity = ".rightAssocNil (parserNil " + term.str() + ")";
  }
  else if (op.d_attr == "left-assoc-ns-nil")
  {
    arity = ".leftAssocNonSingletonNil (parserNil " + term.str() + ")";
  }
  else if (op.d_attr == "right-assoc-ns-nil")
  {
    arity = ".rightAssocNonSingletonNil (parserNil " + term.str() + ")";
  }
  else if (op.d_attr == "arg-list")
  {
    // The unary operator gathers all of its explicit arguments into a list,
    // e.g. `(distinct a b c)` denotes `(distinct (@tlist a b c))`.
    std::string consTerm = getParserOpTerm(op.d_connector);
    if (!consTerm.empty())
    {
      arity = ".argList (fun ts => Logos.Parser.rightAssocNil Term.Apply "
              + consTerm + " (parserNil " + consTerm + ") ts)";
    }
  }
  else if (op.d_attr == "chainable" || op.d_attr == "pairwise")
  {
    std::string connectorTerm = getParserOpTerm(op.d_connector);
    if (!connectorTerm.empty())
    {
      arity = "." + op.d_attr
              + " (fun ts => Logos.Parser.rightAssocNil Term.Apply "
              + connectorTerm + " (parserNil " + connectorTerm + ") ts)";
    }
  }
  if (arity.empty())
  {
    std::stringstream exact;
    exact << ".exact " << op.d_termArity;
    arity = exact.str();
  }
  // `Logos.Parser.Arity` does not model every argument-list attribute. No
  // signature compiled so far uses one of these; warn rather than silently
  // emit Lean that will not compile.
  if (arity.rfind(".leftAssocNil", 0) == 0 || arity.rfind(".pairwise", 0) == 0
      || arity.find("NonSingletonNil") != std::string::npos)
  {
    Warning() << "Lean parser: operator " << name
              << " has argument-list attribute " << op.d_attr
              << ", which Logos.Parser.Arity does not model" << std::endl;
  }

  ops << "  { name := " << quoteLeanString(name) << std::endl;
  ops << "    indexArity := " << op.d_indexArity << std::endl;
  ops << "    arity := " << arity << std::endl;
  ops << "    build := fun" << std::endl;
  ops << "      | [";
  for (size_t i = 0; i < op.d_indexArity; ++i)
  {
    if (i > 0)
    {
      ops << ", ";
    }
    ops << "x" << (i + 1);
  }
  ops << "] => some " << term.str() << std::endl;
  ops << "      | _ => none }," << std::endl;
}

bool LeanMetaReduce::isEmittedParserOp(const ParserOp& op) const
{
  return d_emittedUserOps.find(
             std::make_pair(cleanSmtId(op.d_generated), op.d_indexArity))
         != d_emittedUserOps.end();
}

void LeanMetaReduce::finalizeParser()
{
  // The operators that the parser template declares itself, which a definition
  // of the same name does not override. Keep in sync with the head of
  // plugins/lean_meta/lean_meta_parser.lean.
  std::set<std::string> opNames = {"Type", "Bool", "false", "true", "->",
                                   "@list"};
  std::stringstream ops;
  std::set<std::string> seenOps;
  for (const ParserOp& op : d_parserOps)
  {
    if (!isEmittedParserOp(op))
    {
      continue;
    }
    std::stringstream opKey;
    opKey << op.d_surface << "\n" << cleanSmtId(op.d_generated) << "\n"
          << op.d_indexArity << "\n" << op.d_termArity << "\n" << op.d_attr;
    if (!seenOps.insert(opKey.str()).second)
    {
      continue;
    }
    printParserOp(op, op.d_surface, ops);
    opNames.insert(op.d_surface);
  }

  std::stringstream rules;
  std::set<std::string> seenRules;
  bool firstRule = true;
  for (const std::pair<std::string, std::string>& rule : d_parserRules)
  {
    std::string generated = cleanSmtId(rule.second);
    if (d_emittedRules.find(generated) == d_emittedRules.end()
        || !seenRules.insert(rule.first).second)
    {
      continue;
    }
    if (!firstRule)
    {
      rules << "," << std::endl;
    }
    firstRule = false;
    rules << "  (" << quoteLeanString(rule.first) << ", ." << generated << ")";
  }
  if (!firstRule)
  {
    rules << std::endl;
  }

  std::stringstream defMacros;
  finalizeParseDefs(opNames, ops, defMacros);

  const std::string outPath = emitResourceFile(
      "plugins/lean_meta/lean_meta_parser.lean",
      "plugins/lean_meta/lean_meta_parser_gen.lean",
      {{"$LEAN_PARSER_OPS$", ops.str()},
       {"$LEAN_PARSER_RULES$", rules.str()},
       {"$LEAN_PARSER_MACROS$", defMacros.str()}});
  Trace("lean-meta") << "Write lean parser " << outPath << std::endl;
}

void LeanMetaReduce::finalizeParseDefs(const std::set<std::string>& opNames,
                                       std::ostream& ops,
                                       std::ostream& macros)
{
  std::set<std::string> seen;
  for (const std::pair<std::string, Expr>& d : d_parseDefs)
  {
    const std::string& surface = d.first;
    if (!seen.insert(surface).second)
    {
      continue;
    }
    Expr body = d.second;
    std::vector<Expr> params;
    if (body.getKind() == Kind::LAMBDA)
    {
      Assert(body[0].getKind() == Kind::TUPLE);
      for (size_t i = 0, nargs = body[0].getNumChildren(); i < nargs; i++)
      {
        params.push_back(body[0][i]);
      }
      body = body[1];
    }
    // The remaining free variables of the body are the implicit parameters of
    // the definition, which Eunoia determines by unification where it is
    // applied. The parser cannot, so such a definition is not preserved.
    std::vector<Expr> fvs = Expr::getVariables(body);
    bool isImplicit = false;
    for (const Expr& v : fvs)
    {
      if (std::find(params.begin(), params.end(), v) == params.end())
      {
        isImplicit = true;
        break;
      }
    }
    if (isImplicit)
    {
      Trace("lean-meta") << "Lean parser: omit definition " << surface
                         << ", which has an implicit parameter" << std::endl;
      continue;
    }
    if (params.empty() && opNames.find(surface) != opNames.end())
    {
      // The generic parser distinguishes the declarations of a name by their
      // index and argument counts, so a nullary operator cannot shadow an
      // operator of the same name the way a definition does in Eunoia. The
      // declaration of the signature is kept, which agrees with the definition
      // whenever the latter is an alias for it, as it is in practice.
      Trace("lean-meta") << "Lean parser: omit definition " << surface
                         << ", which is also declared as an operator"
                         << std::endl;
      continue;
    }
    if (params.empty() && body.getNumChildren() == 0)
    {
      // A definition that takes no arguments and whose body is a single
      // operator is an alias for that operator. It is declared as one, rather
      // than bound to the term the operator denotes, so that it inherits the
      // operator's indices and the attribute that combines its arguments: for
      // example the alias of an n-ary operator is itself n-ary.
      std::stringstream ssb;
      ssb << body;
      const ParserOp* op = getParserOpForGenerated(ssb.str());
      if (op != nullptr)
      {
        printParserOp(*op, surface, ops);
        continue;
      }
    }
    // Note we do not let-bind the body, since it is printed as the argument of
    // a constructor below.
    std::stringstream bodyTerm;
    printEmbTerm(body, bodyTerm, MetaKind::NONE, false);
    if (params.empty())
    {
      // A definition that takes no arguments denotes its body. It is declared
      // as a nullary operator, which is how the generic parser's tables name a
      // term; as in Eunoia, it may still be applied to arguments.
      ops << "  { name := " << quoteLeanString(surface) << std::endl;
      ops << "    indexArity := 0" << std::endl;
      ops << "    arity := .exact 0" << std::endl;
      ops << "    build := fun" << std::endl;
      ops << "      | [] => some " << bodyTerm.str() << std::endl;
      ops << "      | _ => none }," << std::endl;
      continue;
    }
    // A definition that takes arguments is a macro, which the parser expands
    // where the definition is applied. Its body is emitted as an operator
    // indexed by the arguments, which is how the generic parser's operator
    // table expresses a term built from given arguments; the macro's body is
    // then just the application of that operator to the macro's parameters.
    std::vector<std::string> binders;
    for (const Expr& v : params)
    {
      std::stringstream ssv;
      ssv << v;
      binders.push_back(cleanSmtId(ssv.str()));
    }
    std::set<std::string> distinct(binders.begin(), binders.end());
    if (distinct.size() < binders.size())
    {
      Warning() << "Lean parser: omit definition " << surface
                << ", whose parameters do not have distinct generated names"
                << std::endl;
      continue;
    }
    const std::string opName = mkParseDefName(surface);
    ops << "  { name := " << quoteLeanString(opName) << std::endl;
    ops << "    indexArity := " << params.size() << std::endl;
    ops << "    arity := .exact 0" << std::endl;
    ops << "    build := fun" << std::endl;
    ops << "      | [";
    for (size_t i = 0, nbinders = binders.size(); i < nbinders; i++)
    {
      ops << (i == 0 ? "" : ", ") << binders[i];
    }
    ops << "] => some " << bodyTerm.str() << std::endl;
    ops << "      | _ => none }," << std::endl;
    macros << "  (" << quoteLeanString(surface) << "," << std::endl;
    macros << "    { params := [";
    std::vector<std::string> args;
    for (size_t i = 0, nparams = params.size(); i < nparams; i++)
    {
      std::stringstream ssa;
      ssa << mkParseDefName("arg") << (i + 1);
      args.push_back(ssa.str());
      macros << (i == 0 ? "" : ", ") << quoteLeanString(args.back());
    }
    macros << "]" << std::endl;
    macros << "      body := .expr [.atom \"_\", .atom "
           << quoteLeanString(opName);
    for (const std::string& a : args)
    {
      macros << ", .atom " << quoteLeanString(a);
    }
    macros << "] })," << std::endl;
  }
}

void LeanMetaReduce::finalizeSmtModel()
{
  std::vector<Replacement> defsRepl{{"$LEAN_SMT_TYPE_DEF$", d_smtTypeDt.str()},
                                    {"$LEAN_SMT_TERM_DEF$", d_smtDt.str()},
                                    {"$LEAN_SMT_VALUE_DEF$",
                                     d_smtValueDt.str()}};
  if (optionSmtTheoryOp())
  {
    // NOTE: enabling this option additionally requires adding an
    // `inductive SmtTheoryOp` block carrying $LEAN_SMT_THEORY_OP_DEF$ to
    // lean_meta_smt_model_defs.lean, ahead of the mutual block that defines
    // SmtTerm. The template has no such block today, so the tag is only
    // supplied when the option is on, where its absence is reported.
    defsRepl.emplace_back("$LEAN_SMT_THEORY_OP_DEF$", d_smtTOpDt.str());
  }
  const std::string outPathDefs =
      emitResourceFile("plugins/lean_meta/lean_meta_smt_model_defs.lean",
                       "plugins/lean_meta/lean_meta_smt_model_defs_gen.lean",
                       defsRepl);
  Trace("lean-meta") << "Write lean-defs " << outPathDefs << std::endl;
  const std::string outPathOrder =
      emitResourceFile("plugins/lean_meta/lean_meta_smt_value_order.lean",
                       "plugins/lean_meta/lean_meta_smt_value_order_gen.lean",
                       {{"$LEAN_SMT_TYPE_KEY$", d_smtTypeKey.str()},
                        {"$LEAN_SMT_VALUE_KEY$", d_smtValueKey.str()}});
  Trace("lean-meta") << "Write lean-order " << outPathOrder << std::endl;
  const std::string outPath =
      emitResourceFile("plugins/lean_meta/lean_meta_smt_model.lean",
                       "plugins/lean_meta/lean_meta_smt_model_gen.lean",
                       {{"$LEAN_SMT_EVAL_DEFS$", d_smtDefs.str()},
                        {"$LEAN_SMT_EVAL$", d_smt.str()}});
  Trace("lean-meta") << "Write lean-defs " << outPath << std::endl;
}

void LeanMetaReduce::finalizeSpec()
{
  const std::string outPath =
      emitResourceFile("plugins/lean_meta/lean_meta_spec.lean",
                       "plugins/lean_meta/lean_meta_spec_gen.lean",
                       {{"$LEAN_EO_IS_OBJ_DEFS$", d_eoIsObjDefs.str()},
                        {"$LEAN_EO_IS_OBJ_SIMPLE_DEFS$", d_eoIsObjDefsSimple.str()}
                      });
  Trace("lean-meta") << "Write lean-defs " << outPath << std::endl;
}

void LeanMetaReduce::finalizeLemmas()
{
  const std::string outPath = emitResourceFile(
      "plugins/lean_meta/lean_meta_rule_lemmas.lean",
      "plugins/lean_meta/lean_meta_rule_lemmas_gen.lean",
      {{"$EO_RULE_LEMMA_INCLUDE$", d_rlInclude.str()},
       {"$EO_RULE_LEMMA_STEP_CASES$", d_rlIncludeStep.str()},
       {"$EO_RULE_LEMMA_STEP_POP_CASES$", d_rlIncludeStepPop.str()}});
  Trace("lean-meta") << "Write lean-defs " << outPath << std::endl;
}

void LeanMetaReduce::finalize()
{
  finalizePrograms();
  // refutation is if the method returns true
  d_eoIsRef << "  | intro (F : Term) (c : CCmdList) : " << std::endl;
  d_eoIsRef << "    (__eo_checker_is_refutation F c) = true -> "
               "(eo_is_refutation F c)"
            << std::endl;

  if (d_ruleDt.str().empty())
  {
    d_ruleDt << "  | none : CRule" << std::endl;
  }
#ifdef INFER_TOTAL_DEFS
  d_defsTotal << "end" << std::endl << std::endl;
  if (d_hasDefs)
  {
    d_defs << "end" << std::endl << std::endl;
  }
#endif

  for (size_t i=0; i<4; i++)
  {
    std::stringstream& etd = d_embedTOpDt[i];
    if (etd.str().empty())
    {
      etd << "  | None : UserOp";
      if (i>0)
      {
        etd << i;
      }
      etd << std::endl;
    }
  }
  finalizeChecker();
  if (d_generateParser)
  {
    finalizeParser();
  }
  finalizeSmtModel();
  finalizeSpec();
  finalizeLemmas();
}

void LeanMetaReduce::printStepCase(std::ostream& out,
                                   const std::string& prule,
                                   bool isPop)
{
  std::stringstream thmName;
  thmName << (isPop ? "" : "exact ") << "cmd_step_" << (isPop ? "pop_" : "")
          << prule << "_properties";
  out << "  | " << prule << " =>" << std::endl;
  out << "      exact cmd_step_" << (isPop ? "pop_" : "")
      << "facts_of_rule_properties";
  out << (isPop ? " M hM root tail A premises hsRoot hsRootStable hSuffix "
                : " M hM s premises hs hsStable ")
      << "<|" << (isPop ? "" : " by") << std::endl;
  if (!isPop)
  {
    out << "        intro N hN _hAgree" << std::endl;
  }
  out << "        " << thmName.str() << " ";
  if (isPop)
  {
    out << "A root args premises" << std::endl;
    out << "          hATrans hATy hPremisesTrans hPremisesTy hResultTy"
        << std::endl;
  }
  else
  {
    out << "N hN s args premises" << std::endl;
    out << "          (by simpa using hCmdTrans) hPremisesBool hResultTy"
        << std::endl;
  }
  std::stringstream ss;
  ss << "plugins/lean_meta/rules/lean_meta_rule_" << prule << "_gen.lean";
  const std::string resource = isPop
                                   ? "plugins/lean_meta/lean_meta_rule_pop.lean"
                                   : "plugins/lean_meta/lean_meta_rule.lean";
  const std::string outPath =
      emitResourceFile(resource, ss.str(), {{"$EO_RULE$", prule}}, true);
  Trace("lean-meta") << "Write lean-defs rule " << outPath << std::endl;
  //  | contra =>
  //      exact cmd_step_facts_of_rule_properties M s premises hs <|
  //        cmd_step_contra_properties M hM s args premises
  //          (by simpa using hCmdTrans) hPremisesBool hProg
  //  | scope =>
  //      exact cmd_step_pop_facts_of_rule_properties root tail A premises <|
  //        cmd_step_pop_scope_properties A root args premises
  //          hATrans hATy hPremisesTrans hPremisesTy hProg
}

bool LeanMetaReduce::echo(const std::string& msg)
{
  if (msg.compare(0, 15, "lean-parser-op ") == 0)
  {
    std::istringstream in(msg.substr(15));
    ParserOp op;
    if (in >> op.d_surface >> op.d_generated >> op.d_indexArity
           >> op.d_termArity >> op.d_attr >> op.d_connector)
    {
      d_parserOps.push_back(op);
    }
    else
    {
      Warning() << "Malformed lean parser operator metadata: " << msg
                << std::endl;
    }
    return false;
  }
  if (msg.compare(0, 17, "lean-parser-rule ") == 0)
  {
    std::istringstream in(msg.substr(17));
    std::string surface;
    std::string generated;
    if (in >> surface >> generated)
    {
      d_parserRules.emplace_back(surface, generated);
    }
    else
    {
      Warning() << "Malformed lean parser rule metadata: " << msg
                << std::endl;
    }
    return false;
  }
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
      EO_FATAL() << "When making Lean theorem, could not find program " << eosc;
    }
    std::string progName = cleanId(eosc);
    ConjectureType ctype = MetaReducePlugin::optionMetaConjectureType();
    if (ctype == ConjectureType::VC)
    {
      const std::string progPrefix = cleanId("$eo_prog_");
      if (progName.compare(0, progPrefix.size(), progPrefix) != 0
          || progName.size() == progPrefix.size())
      {
        EO_FATAL() << "Malformed lean-meta program name " << eosc
                   << "; expected $eo_prog_<rule>";
      }
      std::string prule = progName.substr(progPrefix.size());
      std::string fileName = prule;
      fileName[0] = static_cast<char>(
          std::toupper(static_cast<unsigned char>(fileName[0])));
      d_rlInclude << "import $EO_CALC$.Proofs.Rules." << fileName << std::endl;
      // TODO: don't hardcode this
      if (prule == "scope")
      {
        printStepCase(d_rlIncludeStepPop, prule, true);
      }
      else
      {
        printStepCase(d_rlIncludeStep, prule, false);
      }
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

std::string LeanMetaReduce::quoteLeanString(const std::string& value)
{
  std::stringstream out;
  out << '"';
  for (char c : value)
  {
    switch (c)
    {
      case '\\': out << "\\\\"; break;
      case '"': out << "\\\""; break;
      case '\n': out << "\\n"; break;
      case '\r': out << "\\r"; break;
      case '\t': out << "\\t"; break;
      default: out << c; break;
    }
  }
  out << '"';
  return out.str();
}

}  // namespace ethos
