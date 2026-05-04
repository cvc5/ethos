/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef DESUGAR_CHECKER_H
#define DESUGAR_CHECKER_H

#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

class State;

/**
 * Helper for generating the desugared executable proof checker.
 *
 * `DesugarChecker` is used by the main desugar plugin when VC generation is
 * disabled.  It inspects each proof-rule declaration, emits an embedded rule
 * constant for it, and generates checker invocation cases that translate
 * checker commands into calls to the corresponding desugared proof-rule
 * program.  The accumulated fragments are finally spliced into
 * `eo_desugar_checker.eo` by output().
 */
class DesugarChecker : public StdPlugin
{
 public:
  /** Construct the checker generator and initialize common constants. */
  DesugarChecker(State& s);
  /** Destroy the checker generator. */
  ~DesugarChecker();
  /** Generate embedded rule and invocation cases for proof rule v. */
  void finalizeRule(const Expr& v);

  /** Write the generated checker EO fragment to out. */
  void output(std::ostream& out);

 private:
  /** Common true literal used to recognize assumption rules. */
  Expr d_true;
  /** Generated embedded rule declarations. */
  std::stringstream d_rules;
  /** Generated checker invocations for ordinary proof-rule steps. */
  std::stringstream d_ruleInvokes;
  /** Generated checker invocations for assumption-pop proof-rule steps. */
  std::stringstream d_ruleInvokesPop;
};

}  // namespace ethos

#endif /* DESUGAR_CHECKER_H */
