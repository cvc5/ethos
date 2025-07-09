/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef FLATTEN_EVAL_H
#define FLATTEN_EVAL_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

class State;
class TypeChecker;

class ProgramOut
{
public:

  std::stringstream d_ss;
  size_t d_variant;
};

/**
 * Provides utilities for "flattening" evaluation.
 * At the moment we only define a utility method and don't use this as a standalone plugin.
 */
class FlattenEval : public StdPlugin
{
 public:
  FlattenEval(State& s);
  ~FlattenEval();

  /**
   * Flattens the evaluation in the body of a case of the definition of program v.
   * Introduces auxiliary programs to do so.
   */
  static std::vector<ProgramOut> flattenEval(const Expr& v, const Expr& caseBody, std::ostream& os);
  /**
   * True if this is an invocation of evaluation.
   */
  static bool isEvaluationApp(const Expr& e);
  /**
   * Given a term e, return a term that has no evaluation.
   * For each top-level evaluation term in e, we replace it by a fresh parameter.
   * We track a visited cache, and record new variables introduced in this manner.
   */
  static Expr mkPurifyEvaluation(const Expr& e, std::map<Expr, Expr>& visited, size_t& vcount, std::map<Expr, Expr>& newVars);
};

}  // namespace ethos

#endif /* FLATTEN_EVAL_H */
