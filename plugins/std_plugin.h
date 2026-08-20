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

/**
 * The purpose of this plugin is to do things that are common to multiple
 * plugins. For example, tracking the dependencies for literal types.
 */
class StdPlugin : public Plugin
{
 public:
  StdPlugin(State& s);
  ~StdPlugin();

 protected:
  /** Allocate a fresh type variable */
  Expr allocateTypeVariable();
  /** Get ground term for kind */
  Expr getGroundTermForLiteralKind(Kind k);
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  /** Get the subterms of a kind */
  std::vector<Expr> getSubtermsKind(Kind k, const Expr& t);
  /** Get the name of the literal kind k, e.g. "<numeral>" for NUMERAL. */
  static std::string literalKindToString(Kind k);
  /** Replace the first occurrence of tag in txt by replacement. */
  static void replace(std::string& txt,
                      const std::string& tag,
                      const std::string& replacement);
  /** Replace all occurrences of from in str by to and return the result. */
  static std::string replace_all(std::string str,
                                 const std::string& from,
                                 const std::string& to);
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** type variable counter */
  size_t d_typeVarCounter;
  /**
   * The root directory containing the plugin resource files, i.e. the
   * templates a plugin reads. Taken from ETHOS_PLUGIN_ROOT if set, else from
   * the compile-time definition ETHOS_PLUGIN_SOURCE_DIR supplied by the build.
   */
  static std::string s_plugin_path;
  /**
   * The root directory where generated artifacts are written. Taken from
   * ETHOS_PLUGIN_OUTPUT_DIR if set, else from the compile-time definition of
   * the same name supplied by the build.
   */
  static std::string s_plugin_output_path;
  /** Determine the root containing the plugin resources */
  static std::string initializePluginPath();
  /** Determine the default directory for generated artifacts */
  static std::string initializePluginOutputPath();
  /** Get a path relative to the source resource root */
  static std::string getResourcePath(const std::string& relativePath);
  /** Get a path relative to the generated output root */
  static std::string getOutputPath(const std::string& relativePath);
  /** Copy a static resource into the generated output tree */
  static void copyResourceToOutput(const std::string& relativePath);
  //--------- standard configurations for the reduction
  /** Strict VC mode, i.e. we are not debugging completeness. */
  static bool optionVcUseModelStrict();
  /** Whether to use triggers (:pattern) in the final encoding. */
  static bool optionSmtMetaUseTriggers();
  /** Whether to emit the conjecture in a form easy to debug via models. */
  static bool optionSmtMetaDebugConjecture();
  /** Whether to optimize SyGuS conjectures with a grammar. */
  static bool optionSmtMetaSygusGrammar();
  /** Whether the SyGuS grammar is designed to enumerate well-typed terms. */
  static bool optionSmtMetaSygusGrammarWellTyped();
  /** Whether we emit typing for partial applications. */
  static bool optionEoTypeofHo();
  /** Whether we combine terms of the same type when defining eo::typeof. */
  static bool optionEoTypeCanonize();
  /**
   * Whether we use custom definitions of is_list_nil for operators with
   * non-ground nil terminators.
   */
  static bool optionFwdDeclIsListNilNground();
  /**
   * Whether theory symbols are first-order in the final embedding, e.g.
   * (and : SmtTerm -> SmtTerm -> SmtTerm) instead of (and : SmtTerm).
   */
  static bool optionSmtFoTheorySymbols();
  /** Whether to collapse atomic theory operators into SmtTheoryOp. */
  static bool optionSmtTheoryOp();
  /** Whether to collapse atomic user operators into UserOp. */
  static bool optionEoUserOp();
};

}  // namespace ethos

#endif /* STD_PLUGIN_H */
