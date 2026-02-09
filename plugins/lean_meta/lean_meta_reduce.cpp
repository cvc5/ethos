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

namespace ethos {


LeanMetaReduce::LeanMetaReduce(State& s) : StdPlugin(s)
{
  d_prefixToMetaKind["eo"] = MetaKind::EUNOIA;
  d_prefixToMetaKind["sm"] = MetaKind::SMT;
  d_prefixToMetaKind["tsm"] = MetaKind::SMT_TYPE;
  d_prefixToMetaKind["vsm"] = MetaKind::SMT_VALUE;
  d_prefixToMetaKind["msm"] = MetaKind::SMT_MAP;
  d_prefixToMetaKind["ssm"] = MetaKind::SMT_SEQ;
  d_typeToMetaKind["$eo_Type"] = MetaKind::EUNOIA;
  d_typeToMetaKind["$smt_Term"] = MetaKind::SMT;
  d_typeToMetaKind["$smt_Type"] = MetaKind::SMT_TYPE;
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
    case MetaKind::SMT_VALUE: os << "Term"; break;
    case MetaKind::SMT_BUILTIN: os << getEmbedName(t); break;
    case MetaKind::SMT_MAP: os << "msm.Map"; break;
    case MetaKind::SMT_SEQ: os << "ssm.Seq"; break;
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
      os << "Term." << cname;
    }
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
        os << "(smt_- " << cin.toString() << ")";
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
      os << c;
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
  std::stringstream ss;
  ss << "smt_" << l->d_str.toString();
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
    MetaKind child  = getMetaKindReturn(recTerm, parent);
    Assert(child != MetaKind::NONE)
        << "Failed to get child context for " << recTerm;
    // Trace("lean-meta") << "print: " << recTerm << " (" << ck << "), "
    //           << metaKindToString(parent) << " / "
    //           << metaKindToString(child) << std::endl;
    // We now should only care about the child context!!!
    // if we are printing the head of the term
    if (ck == Kind::PARAM)
    {
      os << recTerm;
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
        Assert(child == MetaKind::EUNOIA);
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
      os << "(Apply (Apply FunType ";
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
  decl << "def " << v << " : ";
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
    Trace("lean-meta") << "Print meta type " << vt[i - 1] << std::endl;
    printMetaType(vt[i - 1], argType, MetaKind::EUNOIA);
    decl << argType.str() << " -> ";
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
      cases << "  | ";
      for (size_t j = 1; j < nargs; j++)
      {
        if (j>1)
        {
          cases << ", ";
        }
        if (i==j)
        {
          cases << "Stuck ";
        }
        else
        {
          cases << "_ ";
        }
      }
      cases << " => Stuck" << std::endl;
    }
  }
  size_t ncases = prog.getNumChildren();
  SelectorCtx ctx;
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
    }
    cases << " => ";
    MetaKind bodyInitCtx = vctxArgs[nargs - 1];
    printEmbTerm(body, cases, bodyInitCtx);
    cases << std::endl;
  }
  if (isEunoiaProgram)
  {
    cases << "  | _ => Stuck" << std::endl;
  }
  // axiom
  d_defs << decl.str();
  d_defs << cases.str();
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
      d_defs << "def " << name << " : Term";
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
  std::stringstream cname;
  // get the meta-kind based on its name
  std::string cnamek;
  MetaKind tk = getMetaKind(d_state, e, cnamek);
  cname << cnamek;
  if (tk == MetaKind::EUNOIA)
  {
    out = &d_embedTermDt;
  }
  else if (tk == MetaKind::SMT_TYPE)
  {
    out = &d_embedTermDt;
  }
  else if (tk == MetaKind::SMT)
  {
    out = &d_embedTermDt;
  }
  else if (tk == MetaKind::SMT_VALUE)
  {
    //out = &d_embedValueDt;
    out = nullptr;
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
  (*out) << cname.str() << " : ";
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
  std::stringstream sygusArgs;
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
    (*out) << sst.str() << " -> ";
    sygusArgs << " G_" << sst.str();
    //(*out) << "; Printing datatype argument type " << typ << " gives \"" <<
    // sst.str() << "\" " << termKindToString(tk) << std::endl;
  }
  (*out) << "Term" << std::endl;
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
  bool success;
  do {
    success = false;
    auto pos = finalLean.find("$");
    if (pos != std::string::npos)
    {
      finalLean.replace(pos, 1, "__");
      success = true;
    }
  } while (success);

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
    Expr def = d_state.getProgram(vv.getValue());
    Assert(!def.isNull());
    Expr patCall = def[0][0];
    Assert(!patCall.isNull());
    d_thms << "/- correctness theorem for " << eosc << " -/" << std::endl;
    // NOTE: this is intentionally quantifying on sm.Term, not eo.Term.
    // In other words, this conjectures that there is an sm.Term, that
    // when embedded into Eunoia witnesses the unsoundness.
    Expr vt = d_tc.getType(vv);
    std::stringstream varList;
    std::stringstream eoTrue;
    std::stringstream call;
    eoTrue << "(Term.Boolean true)";
    Assert(vt.getKind() == Kind::PROGRAM_TYPE);
    Assert(patCall.getNumChildren() == vt.getNumChildren());
    size_t nargs = vt.getNumChildren();
    ConjectureType ctype = StdPlugin::optionSmtMetaConjectureType();
    if (ctype == ConjectureType::VC)
    {
      d_thms << "theorem correct_" << eosc << " : ";
      if (nargs>1)
      {
        d_thms << "forall";
        for (size_t i = 1; i < nargs; i++)
        {
          call << " x" << i;
        }
        d_thms << call.str() << " : Term, ";
      }
      d_thms << "(" << eosc << call.str() << ") != " << eoTrue.str() << " :=" << std::endl;
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

bool LeanMetaReduce::isSmtLibExpression(MetaKind ctx)
{
  return ctx == MetaKind::SMT || ctx == MetaKind::SMT_TYPE
         || ctx == MetaKind::SMT_VALUE;
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
  else if (sname.compare(0, 5, "$smd_") == 0)
  {
    cname = sname.substr(5);
    return MetaKind::EUNOIA;
  }
  cname = sname;
  // If not a distinguished symbol, it may be an SMT-LIB term or a type.
  // Check the type of e.
  Expr c = e;
  Expr tc = s.getTypeChecker().getType(c);
  while (tc.getKind() == Kind::FUNCTION_TYPE)
  {
    tc = tc[tc.getNumChildren() - 1];
  }
  if (tc.getKind() == Kind::TYPE)
  {
    return MetaKind::SMT_TYPE;
  }
  return MetaKind::SMT;
}

MetaKind LeanMetaReduce::getMetaKindArg(const Expr& parent,
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
      Trace("lean-meta") << "Get type meta kind for " << ftype.first[i - 1]
                        << std::endl;
      Expr atype = ftype.first[i - 1];
      if (atype.getKind() == Kind::QUOTE_TYPE)
      {
        Expr qt = atype[0];
        atype = d_tc.getType(qt);
      }
      Trace("lean-meta") << "...process to " << atype << std::endl;
      tknew = getTypeMetaKind(atype);
      Assert(tknew != MetaKind::NONE);
      return tknew;
    }
    if (sname.compare(0, 11, "$smt_apply_") == 0)
    {
      if (i == 1)
      {
        // SMT-LIB identifier
        tk = MetaKind::NONE;
      }
      else
      {
        std::string esname = getEmbedName(parent);
        if (esname == "=")
        {
          MetaKind k1 = getMetaKindReturn(parent[2], parentCtx);
          MetaKind k2 = getMetaKindReturn(parent[3], parentCtx);
          if (k1 == k2)
          {
            // both sides have no context.
            // this allows SMT-LIB equality to operate on any datatype used in
            // the embedding
            tk = MetaKind::NONE;
          }
          else if (k1 == MetaKind::EUNOIA || k2 == MetaKind::EUNOIA)
          {
            // if they have different types, we must "connect" them through the
            // top-level Eunoia datatype
            tk = MetaKind::EUNOIA;
          }
          else
          {
            Assert(false) << "Could not infer argument context for equality";
          }
        }
        else if (esname == "ite")
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
        else if (esname.compare(0, 3, "$eo") == 0)
        {
          // special case: if we are specifying that we should be applying
          // an $eo function, we are Eunoia. This only is used when desugaring
          // proof steps currently.
          tk = MetaKind::EUNOIA;
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
    else
    {
      tk = MetaKind::EUNOIA;
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

bool LeanMetaReduce::isProgramApp(const Expr& app)
{
  return (app.getKind() == Kind::APPLY
          && app[0].getKind() == Kind::PROGRAM_CONST);
}

MetaKind LeanMetaReduce::getMetaKindReturn(const Expr& child, MetaKind parentCtx)
{
  Assert(!child.isNull()) << "null term for meta kind";
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
      std::string esname = getEmbedName(child);
      if (esname == "=")
      {
        // builtin equality returns an SMT-LIB builtin
        MetaKind tk = MetaKind::SMT_BUILTIN;
        MetaKind k1 = getMetaKindReturn(child[2], parentCtx);
        MetaKind k2 = getMetaKindReturn(child[3], parentCtx);
        Assert(k1 == MetaKind::EUNOIA || k2 == MetaKind::EUNOIA || k1 == k2)
            << "Equal sides have incompatible meta types " << child << " "
            << metaKindToString(k1) << " " << metaKindToString(k2);
        return tk;
      }
      if (esname == "ite")
      {
        Assert(child.getNumChildren() == 5);
        MetaKind tk = getMetaKindReturn(child[3], parentCtx);
        MetaKind k2 = getMetaKindReturn(child[4], parentCtx);
        Assert(tk == k2) << "ITE branches have different meta types " << child
                         << " " << metaKindToString(tk) << " and "
                         << metaKindToString(k2);
        return tk;
      }
      else if (esname.compare(0, 3, "$eo") == 0)
      {
        // special case: if we are specifying that we should be applying
        // an $eo function, we are Eunoia. This only is used when desugaring
        // proof steps currently.
        return MetaKind::EUNOIA;
      }
      else
      {
        return MetaKind::SMT_BUILTIN;
      }
    }
    else if (sname.compare(0, 10, "$smt_type_") == 0)
    {
      return MetaKind::SMT_TYPE;
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
    else
    {
      // an opaque application of a user symbol, it depends on
      // its classification via getMetaKind
      std::string tmp;
      return getMetaKind(d_state, child[0], tmp);
    }
  }
  else if (k == Kind::BOOL_TYPE)
  {
    // the Bool type is Eunoia Bool. use ($smt.type_0 "Bool") for builtin
    // SMT-LIB Bool
    return MetaKind::EUNOIA;
  }
  else if (isLiteral(k))
  {
    // TODO: is this right?? whereas Boolean is implicitly SMT?
    return MetaKind::EUNOIA;
  }
  else if (k == Kind::PROGRAM_CONST)
  {
    return MetaKind::PROGRAM;
  }
  else if (k == Kind::FUNCTION_TYPE || k == Kind::TYPE)
  {
    // for now, function type is assumed to be Eunoia.
    // likely HO smt would change this.
    return MetaKind::EUNOIA;
  }
  else if (isLiteralOp(k))
  {
    return MetaKind::EUNOIA;
  }
  else if (hd.getNumChildren() == 0)
  {
    Trace("lean-meta") << "getMetaKindReturn: atomic term " << hd << std::endl;
    std::string sname = getName(hd);
    Expr htype = d_tc.getType(hd);
    Assert(!htype.isNull()) << "Failed to type check " << hd;
    // Nullary deep embedding constructors
    if (sname.compare(0, 5, "$smd_") == 0)
    {
      MetaKind tknew = getTypeMetaKind(htype);
      Trace("lean-meta") << "...use datatype embedding name, got "
                        << metaKindToString(tknew) << std::endl;
      Assert(tknew != MetaKind::NONE);
      return tknew;
    }
    MetaKind tk = getTypeMetaKind(htype);
    Trace("lean-meta") << "...type for atomic term " << hd << " (" << k
                      << ") is " << htype << ", thus context is "
                      << metaKindToString(tk) << std::endl;
    // if it is a Eunoia constant, it depends on the naming
    // convention
    if (k == Kind::CONST && tk == MetaKind::EUNOIA)
    {
      // otherwise, use the meta kind utility.
      std::string cnameTmp;
      tk = getMetaKind(d_state, hd, cnameTmp);
      Trace("lean-meta") << "...change to meta-kind " << metaKindToString(tk)
                        << std::endl;
      // Trace("lean-meta") << "...evaluate meta-kind side condition returns " <<
      // mm
      //           << ", which is " << metaKindToString(tk) <<
      //           std::endl;
    }
    // if somehow failed?
    if (tk == MetaKind::NONE && parentCtx != MetaKind::NONE)
    {
      Trace("lean-meta") << "...change parent?" << std::endl;
      // otherwise just use the parent type????
      tk = parentCtx;
    }
    return tk;
  }
  else
  {
    Assert(false) << "Unknown apply term kind for getMetaKindReturn: " << k;
  }
  return MetaKind::NONE;
}

std::vector<MetaKind> LeanMetaReduce::getMetaKindArgs(const Expr& parent,
                                                     MetaKind parentCtx)
{
  std::vector<MetaKind> args;
  Trace("lean-meta") << "  MetaArg: " << parent << " / " << parent.getKind()
                    << " / " << metaKindToString(parentCtx) << std::endl;
  for (size_t i = 0, nchild = parent.getNumChildren(); i < nchild; i++)
  {
    MetaKind ctx = getMetaKindArg(parent, i, parentCtx);
    Trace("lean-meta") << "    MetaArgChild: " << metaKindToString(ctx)
                      << " for " << parent[i] << std::endl;
    args.push_back(ctx);
  }
  Trace("lean-meta") << "  MetaArg: end" << std::endl;
  return args;
}

}  // namespace ethos
