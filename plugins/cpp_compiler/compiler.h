/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef COMPILER_H
#define COMPILER_H

#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "plugin.h"

namespace ethos {

class State;

/**
 * Generates C++ which reconstructs parsed Eunoia signatures.
 *
 * The generated Executor initializes a State as if the recorded signatures
 * had been parsed and marks those files as included. It deliberately does not
 * generate specialized type-checking or side-condition evaluation code.
 */
class Compiler : public Plugin
{
 public:
  explicit Compiler(State& s);
  ~Compiler() override;

  void reset() override;
  void pushScope() override;
  void popScope() override;
  void includeFile(const Filepath& path,
                   bool isSignature,
                   bool isReference,
                   const Expr& referenceNf) override;
  void finalizeIncludeFile(const Filepath& path,
                           bool isSignature,
                           bool isReference,
                           const Expr& referenceNf) override;
  void setLiteralTypeRule(Kind k, const Expr& type) override;
  void bind(const std::string& name, const Expr& expr) override;
  void markConstructorKind(const Expr& expr,
                           Attr attr,
                           const Expr& constructor) override;
  void defineProgram(const Expr& symbol, const Expr& program) override;
  void finalize() override;

  /** Return the generated C++ source. */
  std::string toString() const;

 private:
  /** Whether callbacks for the current input file should be recorded. */
  bool isRecording() const;
  /** Ensure that expr is reconstructed and return its generated identifier. */
  size_t writeExpr(const Expr& expr);
  /** Return the generated identifier for an expression already written. */
  std::string getName(const Expr& expr) const;
  /** Record :sorry proof rules after all of their attributes were parsed. */
  void writeProofRuleAttributes();
  /** Quote arbitrary text as a C++ string literal. */
  static std::string quote(const std::string& text);

  State& d_state;
  /** Parser expression scopes; only bindings at level zero are persistent. */
  size_t d_nscopes;
  /** True for each nested input that is a signature. */
  std::vector<bool> d_recordingStack;
  /** Declarations and statements written into Executor::initialize(). */
  std::stringstream d_declarations;
  std::stringstream d_initialize;
  /** Statements written into Executor::showCompiledFiles(). */
  std::stringstream d_config;
  /** Generated identifiers for expressions. */
  std::map<const ExprValue*, size_t> d_exprIds;
  /**
   * Keep generated expressions alive for the duration of compilation. Apart
   * from making d_exprIds safe, this avoids churn in the State expression
   * trie while parser-owned temporary Expr handles are released.
   */
  std::vector<Expr> d_retainedExprs;
  size_t d_nextExprId;
  /** Proof rules are revisited after their trailing attributes are parsed. */
  std::vector<Expr> d_proofRules;
  std::set<const ExprValue*> d_sorryRulesWritten;
};

}  // namespace ethos

#endif /* COMPILER_H */
