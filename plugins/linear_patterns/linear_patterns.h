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
 * Utility for rewriting non-linear EO program patterns into linear patterns.
 *
 * Some target encodings, including Lean pattern matching, require each pattern
 * variable to occur at most once.  `LinearPattern` rewrites repeated variables
 * by replacing later occurrences with fresh parameters and collecting equality
 * guards that enforce the original sharing.  When a guarded case is followed
 * by later cases, linearization may split the original program into helper
 * programs so the old fall-through behavior is preserved.
 *
 * The utility is exposed as static methods because callers typically need a
 * one-shot transformation of an already-built program definition.
 */
class LinearPattern : public StdPlugin
{
 public:
  /** Construct the linear-pattern utility plugin. */
  LinearPattern(State& s);
  /** Destroy the linear-pattern utility plugin. */
  ~LinearPattern();
  /**
   * Linearize patterns in prog whose definition is progDef.
   * This returns a list of programs and their definitions that do
   * not have non-linear patterns.
   */
  static std::vector<std::pair<Expr, Expr>> linearize(State& s,
                                                      const Expr& prog,
                                                      const Expr& progDef);

 private:
  /**
   * Returns a pair (new pattern, condition) where new pattern is linear.
   * If condition is null, then no linearization was necessary.
   */
  static std::pair<Expr, Expr> linearizePattern(State& s, const Expr& pat);
  /** Recursively replace repeated parameters and collect equality guards. */
  static Expr linearizeRec(State& s,
                           const Expr& pat,
                           std::map<Expr, size_t>& params,
                           std::vector<Expr>& conds);
};

}  // namespace ethos

#endif /* LINEAR_PATTERNS_H */
