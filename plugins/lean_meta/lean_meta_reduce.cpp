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

#include "state.h"
#include "../linear_patterns/linear_patterns.h"

namespace ethos {

std::string replace_all(std::string str,
                        const std::string& from,
                        const std::string& to)
{
    if (from.empty()) return str;  // avoid infinite loop

    std::size_t pos = 0;
    while ((pos = str.find(from, pos)) != std::string::npos) {
        str.replace(pos, from.length(), to);
        pos += to.length();  // move past the replacement
    }
    return str;
}

LeanMetaReduce::LeanMetaReduce(State& s) : StdPlugin(s)
{
  d_prefixToMetaKind["eo"] = MetaKind::EUNOIA;
  d_prefixToMetaKind["sm"] = MetaKind::SMT;
  d_prefixToMetaKind["tsm"] = MetaKind::SMT_TYPE;
  d_prefixToMetaKind["vsm"] = MetaKind::SMT_VALUE;
  d_prefixToMetaKind["msm"] = MetaKind::SMT_MAP;
  d_prefixToMetaKind["ssm"] = MetaKind::SMT_SEQ;
  d_typeToMetaKind["$eo_Type"] = MetaKind::EUNOIA;
  d_typeToMetaKind["$smt_Value"] = MetaKind::SMT_VALUE;
  d_typeToMetaKind["$smt_Map"] = MetaKind::SMT_MAP;
  d_typeToMetaKind["$smt_Seq"] = MetaKind::SMT_SEQ;
  d_typeToMetaKind["$smt_BuiltinType"] = MetaKind::SMT_BUILTIN;
}

LeanMetaReduce::~LeanMetaReduce() {}

MetaKind LeanMetaReduce::prefixToMetaKind(const std::string& str) const
{
  std::map<std::string, MetaKind>::const_iterator it =
      d_prefixToMetaKind.find(str);
  if (it != d_prefixToMetaKind.end())
  {
    return it->second;
  }
  Assert(false) << "Bad prefix \"" << str << "\"";
  return MetaKind::NONE;
}

bool LeanMetaReduce::printMetaType(const Expr& t,
                                  std::ostream& os,
                                  MetaKind tctx) const
{
  MetaKind tk = getTypeMetaKind(t, tctx);
  switch (tk)
  {
    case MetaKind::EUNOIA: os << "Term"; break;
    case MetaKind::SMT: os << "Term"; break;
    case MetaKind::SMT_TYPE: os << "Term"; break;
    case MetaKind::SMT_BUILTIN: os << getEmbedName(t); break;
    default: return false;
  }
  return true;
}

void LeanMetaReduce::printEmbAtomicTerm(const Expr& c,
                                       std::ostream& os,
                                       MetaKind parent)
{
  parent = parent == MetaKind::NONE ? MetaKind::EUNOIA : parent;
  Kind k = c.getKind();
  if (k == Kind::TYPE)
  {
    os << "Term.Type";
    return;
  }
  std::string name;
  if (c.getKind()==Kind::PROGRAM_CONST)
  {
    // programs always print verbatim
    std::stringstream ss;
    ss << c;
    os << cleanId(ss.str());
    return;
  }
  bool isSmtBuiltin = (parent == MetaKind::SMT_BUILTIN);
  std::stringstream osEnd;
  if (k == Kind::CONST)
  {
    std::string cname = getName(c);
    os << "Term.";
    std::stringstream ss;
    // if it is an explicit embedding of a datatype, take the suffix
    if (cname.compare(0, 5, "$smd_") == 0)
    {
      ss << cname.substr(5);
    }
    else
    {
      ss << cname;
    }
    os << cleanSmtId(ss.str());
  }
  else if (k == Kind::BOOL_TYPE)
  {
    // Bool is embedded as an SMT type, we have to wrap it explicitly here.
    //if (parent == MetaKind::EUNOIA)
    //{
    //  os << "(eo.SmtType ";
    //  osEnd << ")";
    //}
    os << "Term.Bool";
  }
  else
  {
    // Boolean constants are embedded as an SMT type, we have to wrap it
    // explicitly here.
    //if (parent == MetaKind::EUNOIA)
    //{
    //  os << "(SmtTerm ";
    //  osEnd << ")";
    //}
    const Literal* l = c.getValue()->asLiteral();
    if (l == nullptr)
    {
      Assert(false) << "Unknown atomic term kind " << k;
      return;
    }
    if (k == Kind::BOOLEAN)
    {
      if (!isSmtBuiltin)
      {
        os << "(Term.Boolean ";
        osEnd << ")";
      }
      os << (l->d_bool ? "true" : "false");
    }
    else if (k == Kind::NUMERAL)
    {
      if (!isSmtBuiltin)
      {
        os << "(Term.Numeral ";
        osEnd << ")";
      }
      const Integer& ci = l->d_int;
      if (ci.sgn() == -1)
      {
        const Integer& cin = -ci;
        os << "(-" << cin.toString() << " : smt_Int)";
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
        os << "(Term.Rational ";
        osEnd << ")";
      }
      std::stringstream ss;
      ss << c;
      std::string rstr = ss.str();
      os << "(eo_lit_mk_rational " << replace_all(rstr, "/", " ") << ")";
    }
    else if (k == Kind::BINARY)
    {
      if (!isSmtBuiltin)
      {
        os << "(Term.Binary ";
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
        os << "(Term.String ";
        osEnd << ")";
      }
      os << c;
    }
    else
    {
      Assert(false) << "Unknown atomic term literal kind " << k;
    }
  }
  os << osEnd.str();
}

std::string LeanMetaReduce::getName(const Expr& e)
{
  std::stringstream ss;
  if (e.getNumChildren() == 0)
  {
    ss << e;
  }
  return ss.str();
}

bool LeanMetaReduce::isEmbedCons(const Expr& e)
{
  std::string sname = getName(e);
  return (sname.compare(0, 5, "$smd_") == 0);
}

bool LeanMetaReduce::isSmtApplyApp(const Expr& oApp)
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

bool is_integer(const std::string& s) {
    if (s.empty()) return false;
    for (unsigned char c : s) {
        if (!std::isdigit(c)) return false;
    }
    return true;
}

std::string LeanMetaReduce::getEmbedName(const Expr& oApp)
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
  if (is_integer(smtStr))
  {
    return smtStr;
  }
  std::stringstream ss;
  ss << "eo_lit_" << smtStr;
  return ss.str();
}

bool LeanMetaReduce::printEmbTerm(const Expr& body,
                                 std::ostream& os,
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
      // We handle SMT vs SMT_BUILTIN within that method
      // Trace("lean-meta") << "print emb atomic term: " << recTerm << std::endl;
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
  return true;
}

void LeanMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  finalizeProgram(v, prog);
}

void LeanMetaReduce::finalizeProgram(const Expr& v,
                                    const Expr& prog,
                                    bool isDefine)
{
  // forward declaration, ignore
  if (prog.isNull())
  {
    return;
  }
  // must linearize the patterns
  std::vector<std::pair<Expr, Expr>> linProgs = LinearPattern::linearize(d_state, v, prog);
  if (linProgs.size()>1)
  {
    for (size_t i=0, lsize = linProgs.size(); i<lsize; i++)
    {
      finalizeProgram(linProgs[i].first, linProgs[i].second, isDefine);
    }
    return;
  }
  std::string vname = getName(v);
  Trace("lean-meta") << "*** Setting up program " << v << " / " << !prog.isNull()
                    << std::endl;
  //d_defs << "/- " << (prog.isNull() ? "fwd-decl: " : "program: ") << v
  //       << " -/" << std::endl;
  std::stringstream decl;
  Expr vv = v;
  Expr vt = d_tc.getType(vv);
  std::vector<MetaKind> vctxArgs;
  size_t nargs = vt.getNumChildren();
  for (size_t j = 0; j < nargs; j++)
  {
    vctxArgs.push_back(getTypeMetaKind(vt[j]));
  }
  // Trace("lean-meta") << "Type is " << vt << std::endl;
  decl << "def ";
  printEmbAtomicTerm(v, decl);
  decl << " : ";
  Assert(vt.getKind() == Kind::PROGRAM_TYPE)
      << "bad type " << vt << " for " << v;
  Assert(nargs > 1);
  for (size_t i = 1; i < nargs; i++)
  {
    std::stringstream argType;
    Trace("lean-meta") << "Print meta type " << vt[i - 1] << std::endl;
    printMetaType(vt[i - 1], argType, MetaKind::EUNOIA);
    decl << argType.str() << " -> ";
  }
  std::stringstream retType;
  printMetaType(vt[nargs - 1], retType, MetaKind::EUNOIA);
  decl << retType.str() << std::endl;
  // Trace("lean-meta") << "DECLARE " << decl.str() << std::endl;
  Trace("lean-meta") << "*** FINALIZE " << v << std::endl;
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
    for (size_t i = 1; i < nargs; i++)
    {
      if (getTypeMetaKind(vt[i - 1], MetaKind::EUNOIA)!=MetaKind::EUNOIA)
      {
        continue;
      }
      cases << "  | ";
      for (size_t j = 1; j < nargs; j++)
      {
        if (j>1)
        {
          cases << ", ";
        }
        if (i==j)
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
  size_t ncases = prog.getNumChildren();
  SelectorCtx ctx;
  bool wasDefault = false;
  for (size_t i = 0; i < ncases; i++)
  {
    const Expr& c = prog[i];
    const Expr& hd = c[0];
    const Expr& body = c[1];
    ctx.clear();
    std::stringstream currCase;
    ConjPrint print;
    cases << "  | ";
    Assert(hd.getNumChildren() == nargs);
    wasDefault = true;
    for (size_t j = 1, nhdchild = hd.getNumChildren(); j < nhdchild; j++)
    {
      if (j>1)
      {
        cases << ", ";
      }
      // Print the pattern matching predicate for this argument, all
      // concatenated together.
      // Initial context depends on the kind of the argument type of the
      // program.
      MetaKind ctxPatMatch = vctxArgs[j - 1];
      printEmbTerm(hd[j], cases, ctxPatMatch);
      // note this further assumes variables are unique as they are required
      // to be unique at this point
      if (hd[j].getKind()!=Kind::PARAM)
      {
        wasDefault = false;
      }
    }
    cases << " => ";
    MetaKind bodyInitCtx = vctxArgs[nargs - 1];
    printEmbTerm(body, cases, bodyInitCtx);
    cases << std::endl;
  }
  if (isEunoiaProgram && !wasDefault)
  {
    cases << "  | ";
    for (size_t j = 1; j < nargs; j++)
    {
      if (j>1)
      {
        cases << ", ";
      }
      cases << "_";
    }
    cases << " => Term.Stuck" << std::endl;
  }
  // axiom
  d_defs << decl.str();
  d_defs << cases.str();
  //d_defs << "decreasing_by sorry" << std::endl;
  d_defs << std::endl;
  d_defs << std::endl;
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
      Trace("lean-meta") << "Look at define " << name << std::endl;
      // if we fail to type check, just allocate a type variable
      // retType = retType.isNull() ? allocateTypeVariable() : retType;
      Expr retType = allocateTypeVariable();
      Expr pt = d_state.mkProgramType(argTypes, retType);
      Trace("lean-meta") << "....make program " << name
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
      Trace("lean-meta") << "...do program " << tmp << " / " << prog
                        << " instead" << std::endl;
      finalizeProgram(tmp, prog, true);
      Trace("lean-meta") << "...finished lambda program" << std::endl;
    }
    else
    {
      d_defs << "def " << cleanId(name) << " : Term";
      d_defs << " := ";
      printEmbTerm(p, d_defs);
      d_defs << std::endl;
    }
  }
}

void LeanMetaReduce::bind(const std::string& name, const Expr& e)
{
  if (e.getKind() != Kind::CONST)
  {
    return;
  }
  finalizeDecl(e);
}

void LeanMetaReduce::finalizeDecl(const Expr& e)
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
  // get the meta-kind based on its name
  std::string cnamek;
  bool isSmtTerm = false;
  MetaKind tk = getMetaKind(d_state, e, cnamek, isSmtTerm);
  std::string cname = cleanSmtId(cnamek);
  if (tk == MetaKind::EUNOIA)
  {
    out = &d_embedTermDt;
  }
  if (out == nullptr)
  {
    Trace("lean-meta") << "Do not include " << e << std::endl;
    return;
  }
  Trace("lean-meta") << "Include " << e << std::endl;
  //(*out) << "  /- " << (isEmbedCons(e) ? "smt-cons: " : "user-decl: ") << cnamek
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
  else if (attr == Attr::AMB || attr == Attr::AMB_DATATYPE_CONSTRUCTOR)
  {
    Assert(ct.getNumChildren() == 2);
    nopqArgs = 1;
    retType = ct[1];
  }
  std::stringstream eoIsSmtCall;
  // revert overloads
  if (cnamek.compare(0, 5, "$eoo_")==0)
  {
    size_t firstDot = cnamek.find('.');
    Assert(firstDot != std::string::npos && firstDot > 5);
    cnamek = cnamek.substr(5, firstDot - 5);
  }
  std::string eoIsSmtRet = "(Smt_Term.Id \"" + cnamek + "\")";
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
    if (!printMetaType(typ, sst))
    {
      // Assert(false) << "Failed to get meta-type for " << e;
      // os << e;
      //  otherwise, a user-provided ambiguous or opaque term, use eo_Term
      sst << "Term";
    }
    eoIsSmtCall << "x" << (i+1) << " ";
    std::stringstream eosr;
    eosr << "(smt_Term.Apply " << eoIsSmtRet << " y" << (i+1) << ")";
    eoIsSmtRet = eosr.str();
    (*out) << sst.str() << " -> ";
    //(*out) << "; Printing datatype argument type " << typ << " gives \"" <<
    // sst.str() << "\" " << termKindToString(tk) << std::endl;
  }
  (*out) << "Term" << std::endl;
  // if an SMT term
  if (isSmtTerm)
  {
    d_eoIsSmt << "| " << cname << "_case : "; 
    if (nopqArgs>0)
    {
      d_eoIsSmt << "forall (" << eoIsSmtCall.str() << " : Term) (";
      std::stringstream conds;
      for (size_t i = 0; i < nopqArgs; i++)
      {
        d_eoIsSmt << "y" << (i+1);
        conds << "(eo_is_smt x" << (i+1) << " y" << (i+1) << ") -> ";
      }
      d_eoIsSmt << ": Smt_Term) " << conds.str();
    }
    d_eoIsSmt << "(eo_is_smt ";
    if (nopqArgs>0)
    {
      d_eoIsSmt << "(Term." << cname << eoIsSmtCall.str() << ")";
    }
    else
    {
      d_eoIsSmt << "Term." << cname;
    }
    d_eoIsSmt << " " << eoIsSmtRet << ")";
    d_eoIsSmt << std::endl;
  }
}

void LeanMetaReduce::finalize()
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

  // make the final Lean encoding
  std::stringstream ssi;
  ssi << s_plugin_path << "plugins/lean_meta/lean_meta.lean";
  std::ifstream in(ssi.str());
  std::ostringstream ss;
  ss << in.rdbuf();
  std::string finalLean = ss.str();

  replace(finalLean, "$LEAN_DEFS$", d_defs.str());
  replace(finalLean, "$LEAN_THMS$", d_thms.str());
  replace(finalLean, "$LEAN_TERM_DEF$", d_embedTermDt.str());
  replace(finalLean, "$LEAN_EO_IS_SMT_DEF$", d_eoIsSmt.str());
  
  std::stringstream sso;
  sso << s_plugin_path << "plugins/lean_meta/lean_meta_gen.lean";
  Trace("lean-meta") << "Write lean-defs " << sso.str() << std::endl;
  std::ofstream out(sso.str());
  out << finalLean;
}

bool LeanMetaReduce::echo(const std::string& msg)
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
    d_thms << "/- correctness theorem for " << cleanId(eosc) << " -/" << std::endl;
    std::stringstream call;
    ConjectureType ctype = StdPlugin::optionSmtMetaConjectureType();
    if (ctype == ConjectureType::VC)
    {
      d_thms << "theorem correct_" << cleanId(eosc) << " ";
      Expr def = d_state.getProgram(vv.getValue());
      Expr patCall;
      Expr pfcons = d_state.getVar("$eo_pf");
      Expr pfproven = d_state.getVar("$eo_proven");
      AlwaysAssert(!pfcons.isNull()) << "Could not find proof constructor";
      AlwaysAssert(!pfproven.isNull()) << "Could not find proven constructor";
      if (!def.isNull())
      {
        patCall = def[0][0];
        Assert(!patCall.isNull());
        std::vector<Expr> vars = Expr::getVariables(patCall);
        if (!vars.empty())
        {
          d_thms << "(";
          for (size_t i = 0, nvars = vars.size(); i < nvars; i++)
          {
            call << (i>0 ? " " : "") << vars[i];
          }
          d_thms << call.str() << " : Term)";
        }
        d_thms << " :" << std::endl;
        // premises are assumptions in theorem
        for (size_t i=0, nargs=patCall.getNumChildren(); i<nargs; i++)
        {
          if (patCall[i].getKind()==Kind::APPLY_OPAQUE && patCall[i][0]==pfcons)
          {
            d_thms << "  (eo_model_Bool ";
            printEmbTerm(patCall[i][1], d_thms);
            d_thms << " true) ->" << std::endl;
          }
        }
      }
      else
      {
        d_thms << " :" << std::endl;
        patCall = vv;
      }
      d_thms << "  (Not (eo_model_Bool ";
      Expr provenPatCall = d_state.mkExpr(Kind::APPLY, {pfproven, patCall});
      printEmbTerm(provenPatCall, d_thms);
      d_thms << " false)) :=" << std::endl;
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
  else if (msg.compare(0, 13, "smt-meta-cmd ") == 0)
  {
    std::string eosc = msg.substr(13);
    d_defs << "(echo \"Run " << eosc << "...\")" << std::endl;
    d_defs << eosc << std::endl;
    return false;
  }
  return true;
}

bool LeanMetaReduce::isProgram(const Expr& t)
{
  return (t.getKind() == Kind::PROGRAM_CONST);
}

MetaKind LeanMetaReduce::getTypeMetaKind(const Expr& typ,
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
  std::string sname = getName(typ);
  std::map<std::string, MetaKind>::const_iterator it =
      d_typeToMetaKind.find(sname);
  if (it != d_typeToMetaKind.end())
  {
    return it->second;
  }
  return elseKind;
}

MetaKind LeanMetaReduce::getMetaKind(State& s,
                                    const Expr& e,
                                    std::string& cname,
                                    bool& isSmtTerm) const
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
  else if (sname.compare(0, 5, "$smd_") == 0)
  {
    cname = sname.substr(5);
    return MetaKind::EUNOIA;
  }
  cname = sname;
  // If not a distinguished symbol, it may be an SMT-LIB term or a type.
  // Check the type of e.
  Expr tc = e.getType();
  while (tc.getKind() == Kind::FUNCTION_TYPE)
  {
    tc = tc[tc.getNumChildren() - 1];
  }
  isSmtTerm = (tc.getKind() != Kind::TYPE);
  // even if SMT-LIB term, it is a Eunoia datatype
  return MetaKind::EUNOIA;
}

bool LeanMetaReduce::isProgramApp(const Expr& app)
{
  return (app.getKind() == Kind::APPLY
          && app[0].getKind() == Kind::PROGRAM_CONST);
}

std::string LeanMetaReduce::cleanSmtId(const std::string& id)
{
  if (id=="end")
  {
    return "__eo_end";
  }
  std::string idc = id;
  idc = replace_all(idc, "++", "concat");
  idc = replace_all(idc, "+", "plus");
  idc = replace_all(idc, "-", "neg");
  idc = replace_all(idc, "*", "mult");
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
