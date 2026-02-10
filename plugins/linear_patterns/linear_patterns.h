/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef LINEAR_PATTERNS_H
#define LINEAR_PATTERNS_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

class State;
class TypeChecker;

/**
 * Provides utilities for linearizing patterns
 */
class LinearPattern : public StdPlugin
{
 public:
  LinearPattern(State& s);
  ~LinearPattern();
  /**
   * Linearize patterns in prog whose definition is progDef.
   * This returns a list of programs and their definitions that do
   * not have non-linear patterns.
   */
  static std::vector<std::pair<Expr, Expr>> linearize(
      State& s,
      const Expr& prog,
      const Expr& progDef);
 private:
  /**
   * Returns a pair (new pattern, condition) where new pattern is linear.
   * If condition is null, then no linearization was necessary.
   */
  static std::pair<Expr, Expr> linearizePattern(State& s, const Expr& pat);
  static Expr linearizeRec(State& s, const Expr& pat, std::set<Expr>& params, std::vector<Expr>& conds);
};

}  // namespace ethos

#endif /* LINEAR_PATTERNS_H */
