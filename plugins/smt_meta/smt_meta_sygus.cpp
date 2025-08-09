/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "smt_meta_sygus.h"

#include <fstream>
#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

SmtMetaSygus::SmtMetaSygus(State& s) : StdPlugin(s) {}
SmtMetaSygus::~SmtMetaSygus() {}
void SmtMetaSygus::initializeGrammars()
{
  std::cout << "INITIALIZE grammars" << std::endl;
  d_gisFinalized = false;
  d_gfun = d_state.mkSymbol(Kind::CONST, "Fun", d_state.mkType());
  d_gsmtTerm = d_state.mkSymbol(Kind::CONST, "SmtTerm", d_state.mkType());
  d_gsmtType = d_state.mkSymbol(Kind::CONST, "SmtType", d_state.mkType());
  SygusGrammar* tmp;
  tmp = allocateGrammar("G_eo.Term", "eo.Term");
#if 0
  // all types that can be meta-kinds of opaque arguments must go here
  allocateGrammar("G_sm.Term", "sm.Term");
  allocateGrammar("G_tsm.Type", "tsm.Type");
  allocateGrammar("G_vsm.Value", "vsm.Value");
  tmp = allocateGrammar("G_msm.Map", "msm.Map");
  tmp->d_rules << "(msm.cons G_vsm.Value G_vsm.Value G_msm.Map) (msm.default "
                  "G_vsm.Value)";
  tmp = allocateGrammar("G_ssm.Seq", "ssm.Seq");
  tmp->d_rules << "(ssm.cons G_vsm.Value G_ssm.Seq) ssm.empty";
#endif
  tmp = allocateGrammar("G_Bool", "Bool");
  tmp->d_rules << "true false";
  tmp = allocateGrammar("G_Int", "Int");
  tmp->d_rules << "0 (- G_Int_C) G_Int_C";
  tmp = allocateGrammar("G_RegLan", "RegLan");
  tmp->d_rules
      << "re.all re.none (str.to_re G_String) (re.union G_RegLan G_RegLan)";
  tmp = allocateGrammar("G_Int_C", "Int");
  tmp->d_rules << "1 (+ G_Int_C 1)";
  tmp = allocateGrammar("G_Real", "Real");
  tmp->d_rules << "0.0 (/ G_Int_C G_Int_C) (- (/ G_Int_C G_Int_C))";
  tmp = allocateGrammar("G_String", "String");
  tmp->d_rules << "\"\" (str.++ G_String \"A\") (str.++ G_String \"B\")";

  d_cnameToKind["Bool"] = Kind::TYPE;
  d_cnameToKind["Boolean"] = Kind::BOOLEAN;
  d_cnameToKind["Numeral"] = Kind::NUMERAL;
  d_cnameToKind["Rational"] = Kind::RATIONAL;
  d_cnameToKind["Binary"] = Kind::BINARY;
  d_cnameToKind["String"] = Kind::STRING;
}

void SmtMetaSygus::finalizeGrammars()
{
  std::cout << "FINALIZE grammars" << std::endl;
  d_gisFinalized = true;
  SygusGrammar* sg = getGrammarFor(d_null);
  // add reference to unknown to all eo.Term grammars
  for (std::pair<const Expr, SygusGrammar*>& g : d_grammarTypeAlloc)
  {
    Assert(!g.first.isNull());
    sg->d_rules << g.second->d_gname << " ";
    if (g.first == d_gfun)
    {
      // (partial) function applications
      // g.second->d_rules << "(eo.Apply " << g.second->d_gname << " "
      //                  << sg->d_gname << ") ";
    }
  }
  // resolve all unique references
  for (std::pair<const Expr, std::vector<Expr>>& g : d_grefs)
  {
    SygusGrammar* sg = getGrammarFor(g.first);
    std::set<Expr> processed;
    for (size_t i = 0, nrefs = g.second.size(); i < nrefs; i++)
    {
      Expr aret = g.second[i];
      if (processed.find(aret) != processed.end())
      {
        continue;
      }
      processed.insert(aret);
      SygusGrammar* sgr = getGrammarFor(aret);
      sg->d_rules << sgr->d_gname << " ";
    }
  }
}

SygusGrammar* SmtMetaSygus::allocateGrammar(const std::string& gn,
                                            const std::string& tn)
{
  Assert(!d_gisFinalized);
  d_glist.push_back(gn);
  SygusGrammar& sg = d_grammar[gn];
  sg.d_gname = gn;
  sg.d_typeName = tn;
  return &sg;
}

SygusGrammar* SmtMetaSygus::getGrammar(const std::string& gn)
{
  std::map<std::string, SygusGrammar>::iterator it = d_grammar.find(gn);
  if (it != d_grammar.end())
  {
    return &it->second;
  }
  return nullptr;
}

Expr SmtMetaSygus::getGrammarTypeApprox(const Expr& e)
{
  Expr cur = e;
  while (cur.getKind() == Kind::APPLY)
  {
    cur = cur[0];
  }
  if (cur.getKind() == Kind::QUOTE_TYPE)
  {
    Expr q = cur[0];
    cur = d_tc.getType(q);
  }
  if (!cur.isGround())
  {
    return d_null;
  }
  Kind ck = cur.getKind();
  if (ck == Kind::FUNCTION_TYPE)
  {
    return d_gfun;
  }
  else if (ck == Kind::TYPE || ck == Kind::BOOL_TYPE)
  {
    return cur;
  }
  else if (ck == Kind::CONST)
  {
    std::stringstream ssc;
    ssc << cur;
    std::string cname = ssc.str();
    if (cname == "$eo_Term")
    {
      // special case: those marked $eo_Term are general Eunoia terms
      return d_null;
    }
    else if (cname == "$smt_Type")
    {
      return d_gsmtType;
    }
    return cur;
  }
  else if (ck == Kind::PROGRAM_CONST)
  {
    // unknown case
    return d_null;
  }
  else
  {
    Assert(false) << "Unknown grammar type " << ck << " " << e;
  }
  return d_null;
}

std::vector<Expr> SmtMetaSygus::getGrammarSigApprox(const Expr& t)
{
  std::vector<Expr> ret;
  Expr ct = t;
  while (ct.getKind() == Kind::FUNCTION_TYPE)
  {
    Assert(ct.getNumChildren() == 2);
    ret.push_back(getGrammarTypeApprox(ct[0]));
    ct = ct[1];
  }
  ret.push_back(getGrammarTypeApprox(ct));
  return ret;
}

SygusGrammar* SmtMetaSygus::getGrammarFor(const Expr& t)
{
  if (t.isNull())
  {
    return getGrammar("G_eo.Term");
  }
  std::map<Expr, SygusGrammar*>::iterator itg = d_grammarTypeAlloc.find(t);
  if (itg != d_grammarTypeAlloc.end())
  {
    return itg->second;
  }
  std::stringstream gname;
  gname << "T_" << t;
  SygusGrammar* sg = allocateGrammar(gname.str(), "eo.Term");
  d_grammarTypeAlloc[t] = sg;
  // add the reference in the main Eunoia grammar
  d_grefs[d_null].push_back(t);
  return sg;
}

void SmtMetaSygus::addGrammarRules(const Expr& e,
                                   const std::string& cname,
                                   MetaKind tk,
                                   const std::string& gbase,
                                   const Expr& t)
{
  std::cout << "Add grammar rules " << e << " / " << cname << "..."
            << std::endl;
  std::stringstream grule;
  std::stringstream gruleEnd;
  Expr defaultG;
  if (tk == MetaKind::EUNOIA)
  {
    if (cname == "Stuck" || cname == "SmtTerm" || cname == "SmtType")
    {
      return;
    }
    if (StdPlugin::optionSmtMetaSygusGrammarWellTyped())
    {
      if (cname == "Apply" || cname == "Const")
      {
        return;
      }
    }
  }
  else if (tk == MetaKind::SMT_TYPE)
  {
    if (cname == "NullSort")
    {
      return;
    }
    // print on both
#if 0
    SygusGrammar* sg = getGrammar("G_tsm.Type");
    sg->d_rules << gbase << " ";
#endif
    grule << "(eo.SmtType ";
    gruleEnd << ")";
    defaultG = d_gsmtType;
  }
  else if (tk == MetaKind::SMT)
  {
    // print on both
#if 0
    SygusGrammar* sg = getGrammar("G_sm.Term");
    sg->d_rules << gbase << " ";
#endif
    grule << "(eo.SmtTerm ";
    gruleEnd << ")";
    defaultG = d_gsmtTerm;
  }
  else if (tk == MetaKind::SMT_VALUE)
  {
#if 0
    if (cname != "NotValue")
    {
      SygusGrammar* sg = getGrammar("G_vsm.Value");
      sg->d_rules << gbase << " ";
    }
#endif
    return;
  }
  else if (tk==MetaKind::SMT_MAP || tk==MetaKind::SMT_SEQ)
  {
    return;
  }
  grule << gbase << gruleEnd.str();
  std::map<std::string, Kind>::iterator itk = d_cnameToKind.find(cname);
  Expr ct;
  if (itk == d_cnameToKind.end())
  {
    ct = t;
  }
  else if (itk->second == Kind::TYPE)
  {
    ct = d_state.mkType();
  }
  else if (itk->second == Kind::BOOLEAN)
  {
    ct = d_state.mkBoolType();
  }
  else
  {
    // ensure it is ground by getting an arbitrary value
    Expr gt = getGroundTermForLiteralKind(itk->second);
    ct = d_tc.getOrSetLiteralTypeRule(itk->second, gt.getValue());
  }
  std::vector<Expr> approxSig = getGrammarSigApprox(ct);
  Assert(!approxSig.empty());
  for (size_t i = 0, nsig = approxSig.size(); i < nsig; i++)
  {
    if (approxSig[i].isNull())
    {
      approxSig[i] = defaultG;
    }
  }
  // the return type of this is now marked as a possible sort
  Expr aret = approxSig[approxSig.size() - 1];
  if (!defaultG.isNull() && !aret.isNull() && aret != defaultG)
  {
    // ensure its allocated
    getGrammarFor(defaultG);
    d_grefs[defaultG].push_back(aret);
  }
#if 0
  if (approxSig.size()>1)
  {
    std::cout << "AJR check " << cname << " " << ct << std::endl;
    std::pair<std::vector<Expr>, Expr> ftype = ct.getFunctionType();
    std::vector<Expr>& fargs = ftype.first;
    Assert (approxSig.size()==fargs.size()+1);
    for (size_t i=1, nargs=approxSig.size(); i<nargs; i++)
    {
      if (!approxSig[i-1].isNull())
      {
        continue;
      }
      std::cout << "AJR maybe " << i << " " << fargs << std::endl;
      std::unordered_set<size_t> eqArgs;
      eqArgs.insert(i-1);
      for (size_t j=i, nargs=fargs.size(); j<nargs; j++)
      {
        if (fargs[i-1]==fargs[j])
        {
          eqArgs.insert(j);
        }
      }
      if (eqArgs.size()>1)
      {
        SygusRuleSchema& srs = d_grammarRuleSchema[e];
        srs.d_cname = grule.str();
        srs.d_approxArgs = approxSig;
        srs.d_eqArgs = eqArgs;
        return;
      }
    }
  }
#endif
  // check if we should make this a schema
  std::string curr = grule.str();
  addRulesForSig(curr, approxSig);
  // separately, if there is a constant rule, add it
  // TODO: remove this??
#if 0
  std::map<std::string, std::string>::iterator it = d_gconstRule.find(cname);
  if (it != d_gconstRule.end())
  {
    // get the grammar for this symbol, e.g. T_BitVec
    SygusGrammar* sgc = getGrammarFor(e);
    sgc->d_rules << it->second << " ";
  }
#endif
}

void SmtMetaSygus::addRulesForSig(const std::string& gbase,
                                  const std::vector<Expr>& approxSig)
{
  std::string curr = gbase;
  // if it is a function
  if (approxSig.size() > 1)
  {
    // print it as a standalone function
    SygusGrammar* sg = getGrammarFor(d_gfun);
    sg->d_rules << curr << " ";
    // then, construct a complete application of the symbol, for the
    // approximation
    for (size_t i = 1, nsig = approxSig.size(); i < nsig; i++)
    {
      SygusGrammar* sga = getGrammarFor(approxSig[i - 1]);
      std::stringstream next;
      next << "(eo.Apply " << curr << " " << sga->d_gname << ")";
      curr = next.str();
    }
  }
  // print the complete application
  Expr aret = approxSig[approxSig.size() - 1];
  SygusGrammar* sgret = getGrammarFor(aret);
  sgret->d_rules << curr << " ";
}

void SmtMetaSygus::printGrammar(const std::string& name,
                                const Expr& t,
                                std::ostream& os)
{
  os << std::endl << "  ((G_Start eo.Term)";
  // start with the appropriate non-terminal
  Expr gt = getGrammarTypeApprox(t);
  // if unknown, it is likely a type parameter, in which case we
  // assume we are looking for an SMT-LIB term
  if (gt.isNull())
  {
    gt = d_gsmtTerm;
  }
  SygusGrammar* sggt = getGrammarFor(gt);
  std::stringstream body;
  body << "  (G_Start eo.Term (" << sggt->d_gname << "))" << std::endl;
  for (const std::string& gn : d_glist)
  {
    SygusGrammar& g = d_grammar[gn];
    os << " (" << g.d_gname << " " << g.d_typeName << ")";
    body << "  (" << g.d_gname << " " << g.d_typeName << " (" << g.d_rules.str()
         << "))" << std::endl;
  }
  os << ") (" << std::endl;
  os << body.str();
  os << ")" << std::endl;
}

}  // namespace ethos
