/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef STD_PLUGIN_H
#define STD_PLUGIN_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "plugin.h"
#include "state.h"
#include "type_checker.h"

namespace ethos {

class State;
class TypeChecker;

enum class ConjectureType
{
  VC,
  SYGUS
};
/**
 * The purpose of this plugin is to do things that are common to multiple
 * plugins. For example, tracking the dependencies for literal types.
 */
class StdPlugin : public Plugin
{
 public:
  StdPlugin(State& s);
  ~StdPlugin();
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t) override;
  /**
   * Mark semantics, used for meta-level reasoning.
   */
  void markSemantics(const Expr& c, const Expr& t) override;

 protected:
  Expr lookupVar(const std::string& name);
  /** Allocate a fresh type variable */
  Expr allocateTypeVariable();
  /** Get ground term for kind */
  Expr getGroundTermForLiteralKind(Kind k);
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  /**
   * Finalize a declaration that was made to define a literal type.
   * We can assume that t is ground.
   */
  virtual void finalizeDeclaration(const Expr& t, std::ostream& os);
  /** Get the subterms of a kind */
  std::vector<Expr> getSubtermsKind(Kind k, const Expr& t);
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** Declares processed for lit types */
  std::set<Expr> d_ltDeclProcessed;
  /** type variable counter */
  size_t d_typeVarCounter;
  /** mark semantics */
  std::map<Expr, Expr> d_markedSemantics;

  std::stringstream d_litTypeDecl;
  std::stringstream d_litTypeProg;
  static std::string s_plugin_path;
  /** Standard configurations for the reduction */
  static bool optionFlattenEval();
  static bool optionVcUseTypeof();
  static bool optionVcUseIsInput();
  static bool optionVcUseArgIsInput();
  static bool optionVcUseModelStrict();
  static bool optionSmtMetaUseTriggers();
  static bool optionSmtMetaDebugConjecture();
  ConjectureType optionSmtMetaConjectureType() const;
  static bool optionSmtMetaSygusGrammar();
  static bool optionSmtMetaSygusGrammarWellTyped();
};

}  // namespace ethos

#endif /* STD_PLUGIN_H */
