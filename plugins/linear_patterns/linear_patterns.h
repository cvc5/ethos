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
#include <utility>
#include <vector>

#include "expr.h"

namespace ethos {

class State;

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
 * For example, consider the program below, whose first case matches the two
 * arguments of `and` against the same parameter `x`:
 *
 *   (program $collapse ((x Bool) (y Bool))
 *     :signature (Bool) Bool
 *     (
 *       (($collapse (and x x)) x)
 *       (($collapse (and x y)) (and x y))
 *     )
 *   )
 *
 * The repeated occurrence of `x` becomes the fresh parameter `$eo.lv.x.2`,
 * and the equality it stood for becomes the guard `(eo::eq x $eo.lv.x.2)`.
 * Since the guarded case is not the last one, the guard must be able to fail
 * into the cases that follow it, which a single program cannot express.  The
 * remaining cases therefore move into a continuation program, and the guard
 * is emitted as an `eo::ite` whose else branch calls it:
 *
 *   (program $eo.l.1.$collapse ((x Bool) (y Bool))
 *     :signature (Bool) Bool
 *     (
 *       (($eo.l.1.$collapse (and x y)) (and x y))
 *     )
 *   )
 *   (program $collapse ((x Bool) ($eo.lv.x.2 Bool) ($eo.dv.1 Bool))
 *     :signature (Bool) Bool
 *     (
 *       (($collapse (and x $eo.lv.x.2))
 *        (eo::ite (eo::eq x $eo.lv.x.2)
 *                 x
 *                 ($eo.l.1.$collapse (and x $eo.lv.x.2))))
 *       (($collapse $eo.dv.1) ($eo.l.1.$collapse $eo.dv.1))
 *     )
 *   )
 *
 * The trailing case of `$collapse` is the catch-all that forwards inputs
 * matching none of its patterns to the continuation.  It is required here
 * because `(and x $eo.lv.x.2)` is not fully general: an input that is not an
 * application of `and` would otherwise get stuck instead of reaching the
 * second case.  When the linearized pattern happens to be fully general, that
 * is, when every argument is a plain parameter, the case already matches
 * everything and no catch-all is added.
 *
 * A non-linear pattern in the *last* case needs no split, since there is
 * nothing to fall through to.  Its guard is emitted as an `eo::requires`
 * instead, so the case simply gets stuck when the guard fails:
 *
 *   (($collapse (and x x)) x)
 *   ==>
 *   (($collapse (and x $eo.lv.x.2))
 *    (eo::requires (eo::eq x $eo.lv.x.2) true x))
 *
 * Note the two naming schemes above: `$eo.lv.<param>.<n>` for the parameter
 * standing for the n-th occurrence of `<param>`, `$eo.dv.<i>` for the i-th
 * argument of a catch-all case, and `$eo.l.<n>.<prog>` for the n-th
 * continuation program split off from `<prog>`.
 *
 * Note that `linearize` returns only program symbols paired with their case
 * lists; the `program` declarations shown above are how a consumer renders
 * those pairs, and the parameter lists and signatures are supplied by the
 * consumer rather than by this utility.  Each case pattern is headed by the
 * program that owns it, as `($eo.l.1.$collapse (and x y))` above shows for a
 * case that was carried over from `$collapse`.  Note that the head of a case
 * pattern is ignored when a program is evaluated, so this renaming is
 * immaterial to the semantics; it matters only for consumers that read the
 * head, e.g. to determine which programs a program calls.
 *
 * The utility is exposed as static methods because callers typically need a
 * one-shot transformation of an already-built program definition.
 */
class LinearPattern
{
 public:
  /**
   * Linearize patterns in prog whose definition is progDef.
   * This returns a list of programs and their definitions that do
   * not have non-linear patterns.
   *
   * The first component of each pair is the program symbol and the second is
   * its list of cases.  The original program is always present; splitting a
   * guarded case appends further continuation programs.  The list is ordered
   * so that a program appears after the continuations it calls, although note
   * this is not a topological order in general: if a case of the original
   * program is recursive, then it is called by the continuation that carries
   * that case, and the group is mutually recursive.  A consumer that requires
   * forward declarations must handle this case.
   */
  static std::vector<std::pair<Expr, Expr>> linearize(State& s,
                                                      const Expr& prog,
                                                      const Expr& progDef);

 private:
  /**
   * Returns the case pattern pat with prog as its head, which is pat itself if
   * it is already headed by prog. This ensures each case of a program is
   * headed by that program, see above.
   */
  static Expr mkCasePattern(State& s, const Expr& prog, const Expr& pat);
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
