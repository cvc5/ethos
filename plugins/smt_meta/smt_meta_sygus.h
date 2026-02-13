/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#ifndef PLUGIN_SMT_META_SYGUS_H
#define PLUGIN_SMT_META_SYGUS_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "../std_plugin.h"
#include "state.h"
#include "utils.h"

namespace ethos {

/** for sygus */
class SygusGrammar
{
 public:
  SygusGrammar() {}
  std::string d_gname;
  std::string d_typeName;
  std::stringstream d_rules;
};
class SygusRuleSchema
{
 public:
  SygusRuleSchema() {}
  std::string d_cname;
  std::vector<Expr> d_approxArgs;
  std::unordered_set<size_t> d_eqArgs;
  std::vector<Expr> instantiate(const Expr& g)
  {
    std::vector<Expr> ret = d_approxArgs;
    for (size_t a : d_eqArgs)
    {
      ret[a] = g;
    }
    return ret;
  }
};

/**
 */
class SmtMetaSygus : public StdPlugin
{
 public:
  SmtMetaSygus(State& s);
  ~SmtMetaSygus();
  void initializeGrammars();
  void finalizeGrammars();
  void addGrammarRules(const Expr& e,
                       const std::string& cname,
                       MetaKind tk,
                       const std::string& gbase,
                       const Expr& t);
  void printGrammar(const std::string& name, const Expr& t, std::ostream& os);

 private:
  /** Grammars */
  Expr d_null;
  Expr d_gfun;
  Expr d_gsmtTerm;
  Expr d_gsmtType;
  bool d_gisFinalized;
  std::map<Expr, std::vector<Expr>> d_grefs;
  std::vector<std::string> d_glist;
  std::map<std::string, SygusGrammar> d_grammar;
  std::map<std::string, std::string> d_gconstRule;
  std::map<Expr, SygusGrammar*> d_grammarTypeAlloc;
  std::map<std::string, Kind> d_cnameToKind;
  std::map<Expr, SygusRuleSchema> d_grammarRuleSchema;
  SygusGrammar* allocateGrammar(const std::string& gn, const std::string& tn);
  SygusGrammar* getGrammar(const std::string& gn);
  Expr getGrammarTypeApprox(const Expr& e);
  std::vector<Expr> getGrammarSigApprox(const Expr& e);
  SygusGrammar* getGrammarFor(const Expr& t);
  void addRulesForSig(const std::string& gbase,
                      const std::vector<Expr>& approxSig);
  // checking if SMT-LIB term
  MetaKind getSmtLibMetaKind(const Expr& e) const;
};

}  // namespace ethos

#endif
