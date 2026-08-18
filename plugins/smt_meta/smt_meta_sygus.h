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

/**
 * A non-terminal of a generated SyGuS grammar, that is, one entry of the
 * grammar declaration of a synth-fun command.
 */
class SygusGrammar
{
 public:
  SygusGrammar() {}
  /** The name of the non-terminal, e.g. "G_eo.Term". */
  std::string d_gname;
  /** The SMT-LIB sort of the non-terminal, e.g. "eo.Term". */
  std::string d_typeName;
  /** The accumulated production rules of the non-terminal. */
  std::stringstream d_rules;
};
/**
 * A production-rule schema for a constructor whose argument grammars depend
 * on the grammar it is instantiated for, e.g. a polymorphic constructor whose
 * repeated argument types must all refer to the same non-terminal.
 */
class SygusRuleSchema
{
 public:
  SygusRuleSchema() {}
  /** The (printed) constructor the schema generates rules for. */
  std::string d_cname;
  /**
   * The grammar approximation for each argument (see
   * SmtMetaSygus::getGrammarTypeApprox), where null stands for the grammar
   * the schema is instantiated with.
   */
  std::vector<Expr> d_approxArgs;
  /** The argument positions to instantiate. */
  std::unordered_set<size_t> d_eqArgs;
  /** Return d_approxArgs with the positions in d_eqArgs replaced by g. */
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
 * Companion of SmtMetaReduce that generates a SyGuS grammar for enumerating
 * deeply embedded Eunoia terms. It receives the same declarations as the
 * SMT-LIB backend via addGrammarRules and, when the SyGuS conjecture type is
 * selected, prints a grammar restricting the search space of the synthesized
 * counterexample terms.
 */
class SmtMetaSygus : public StdPlugin
{
 public:
  SmtMetaSygus(State& s);
  ~SmtMetaSygus();
  /** Allocate the builtin grammar non-terminals (literals, eo.Term, etc.). */
  void initializeGrammars();
  /**
   * Called after all declarations have been processed. Connects the
   * type-specific non-terminals to the generic Eunoia term grammar and
   * resolves the cross-references collected in d_grefs.
   */
  void finalizeGrammars();
  /**
   * Register grammar production gbase for the declared constant e, where
   * cname is its name in the final embedding, tk its meta-kind and t its
   * type. Only constants classified as Eunoia terms contribute rules.
   */
  void addGrammarRules(const Expr& e,
                       const std::string& cname,
                       MetaKind tk,
                       const std::string& gbase,
                       const Expr& t);
  /** Print the complete grammar for a synthesis target named name of type t. */
  void printGrammar(const std::string& name, const Expr& t, std::ostream& os);

 private:
  /** The null expression, keys the generic Eunoia term grammar. */
  Expr d_null;
  /** Sentinel standing for the grammar of function-typed arguments. */
  Expr d_gfun;
  /** Sentinel standing for the grammar of embedded SMT-LIB terms. */
  Expr d_gsmtTerm;
  /** Sentinel standing for the grammar of embedded SMT-LIB types. */
  Expr d_gsmtType;
  /** Whether finalizeGrammars has been called. */
  bool d_gisFinalized;
  /**
   * Maps each grammar key to the approximated types its rules reference;
   * the corresponding non-terminals are added in finalizeGrammars.
   */
  std::map<Expr, std::vector<Expr>> d_grefs;
  /** The names of the allocated grammars, in allocation order. */
  std::vector<std::string> d_glist;
  /** Maps grammar names to the grammars themselves. */
  std::map<std::string, SygusGrammar> d_grammar;
  /** Maps constructor names to a dedicated constant production, if any. */
  std::map<std::string, std::string> d_gconstRule;
  /** Maps grammar keys (see getGrammarFor) to their allocated grammar. */
  std::map<Expr, SygusGrammar*> d_grammarTypeAlloc;
  /** Maps embedded literal constructor names to their literal kind. */
  std::map<std::string, Kind> d_cnameToKind;
  /** Maps constructors to their production-rule schemas, if any. */
  std::map<Expr, SygusRuleSchema> d_grammarRuleSchema;
  /** Allocate a fresh grammar named gn whose non-terminal has sort tn. */
  SygusGrammar* allocateGrammar(const std::string& gn, const std::string& tn);
  /** Get the grammar named gn, or nullptr if it does not exist. */
  SygusGrammar* getGrammar(const std::string& gn);
  /**
   * Get the expression keying the grammar that approximates the type e, e.g.
   * a literal type for literals or a sentinel above, or null if terms of
   * type e are covered by the generic Eunoia term grammar.
   */
  Expr getGrammarTypeApprox(const Expr& e);
  /** Get the grammar approximations for all argument types of type t. */
  std::vector<Expr> getGrammarSigApprox(const Expr& t);
  /** Get (or allocate) the grammar keyed by t, where null is the generic
   * Eunoia term grammar. */
  SygusGrammar* getGrammarFor(const Expr& t);
  /**
   * Add the production rule gbase to the grammars determined by the
   * argument approximations approxSig, registering cross-references for
   * finalizeGrammars.
   */
  void addRulesForSig(const std::string& gbase,
                      const std::vector<Expr>& approxSig);
  /**
   * Classify e as an embedded SMT-LIB term (SMT), an embedded SMT-LIB type
   * (SMT_TYPE), or a Eunoia term (EUNOIA), based on its name and type.
   */
  MetaKind getSmtLibMetaKind(const Expr& e) const;
};

}  // namespace ethos

#endif
