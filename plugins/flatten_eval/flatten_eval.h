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

/**
 * Maintains a context for flattening evaluation of programs.
 */
class ProgramOutCtx
{
 public:
  ProgramOutCtx(State& s, const std::string& progPrefix);
  /** Add that a is a pattern argument of programs we are currently considering */
  void pushArg(const Expr& a);
  /** Same as above, with a type */
  void pushArgTyped(const Expr& a, const Expr& at);
  /** Pop the last argument we pushed */
  void popArg();
  /** Get a fresh parameter */
  Expr allocateVariable(const Expr& retType);
  /**
   * Called we require a new program for flattening evaluation.
   * The arguments nvars are temporary pattern variables,
   * nargs are terms to instantiate them, and ret is the return
   * value of the program.
   * This method returns the given call to the program.
   * For example, say we want to flatten the evaluation of
   *   (f x1 x2 (eo::add n1 n2)).
   * Say our current context has arguments {x1, x2}. We call
   * this method with nvars = {x3}, nargs = {(eo::add n1 n2)},
   * ret=(f x1 x2 x3), then we  generate the program:
   *
   * (program $prog_X ((T Type) (x1 T) (x2 T) (x3 T))
   *   :signature (T T T) T
   *   (
   *   (($prog_X x1 x2 x3) (f x1 x2 x3))
   *   )
   * )
   * and return the application ($prog_X x1 x2 (eo::add n1 n2)).
   * This term and the program returned about do not have
   * evaluation nested inside ordinary applications.
   *
   * We additionally ensure that if a term in nargs is an ite,
   * it is flattened in place. For example, if our term to flatten
   * had been:
   *    (f x1 x2 (eo::ite C b1 b2))
   * the same example, we introduce another program:
   *
   * (program $prog_X_ite ((T Type) (x1 T) (x2 T))
   *   :signature (T T Bool) T
   *   (
   *   (($prog_X_ite x1 x2 true)  b1)
   *   (($prog_X_ite x1 x2 false) b2)
   *   )
   * )
   * and return the application ($prog_X x1 x2 ($prog_X_ite C)).
   */
  Expr allocateProgram(const std::vector<Expr>& nvars,
                       const std::vector<Expr>& nargs,
                       const Expr& ret);
  /** Get the current arguments */
  std::vector<Expr> getArgs() { return d_args; }
  std::map<Expr, Expr> d_visited;
  std::vector<std::pair<Expr, Expr>> d_progAlloc;

 private:
  /**
   * This is called on all arguments to introduced programs
   * (e.g. terms in nargs to allocateProgram). This preprocesses
   * them so that e.g. eo::ite is eliminated.
   */
  Expr ensureFinalArg(const Expr& e);
  /**
   * Allocate a program constant based on the current set of
   * arguments and their types.
   */
  Expr allocateProgramInternal(const Expr& retType);
  /** Returns prog applied to the current arguments. */
  Expr mkCurrentProgramPat(const Expr& prog);
  /** Get the type of e, or a dummy type otherwise. */
  Expr getTypeInternal(const Expr& e);
  /** Reference to the state */
  State& d_state;
  /** Current arguments and their type */
  std::vector<Expr> d_args;
  std::vector<Expr> d_argTypes;
  /** Used for naming new parameters and programs */
  std::string d_progPrefix;
  size_t d_varCount;
  size_t d_progCount;
};

/**
 * Provides utilities for "flattening" evaluation.
 * At the moment we only define a utility method and don't use this as a
 * standalone plugin.
 */
class FlattenEval : public StdPlugin
{
 public:
  FlattenEval(State& s);
  ~FlattenEval();
  /**
   * Flatten program prog whose definition is progDef.
   * This returns a list of programs and their definitions that do
   * not have nested evaluation or special control-flow semantics
   * (ite/requires). These programs can be printed in order, such
   * that programs later in the list may rely on those earlier in
   * the list.
   */
  static std::vector<std::pair<Expr, Expr>> flattenProgram(State& s,
                                                           const Expr& prog,
                                                           const Expr& progDef);
  /**
   * Flattens the evaluation in term t, where t may contain
   * free variables.
   */
  static Expr flattenEval(State& s, ProgramOutCtx& ctx, const Expr& t);
  /**
   * Return the index of the child of e beyond which are not immediately
   * evaluated. This is 1 for ite, 2 for requires, and e.getNumChildren()
   * otherwise.
   */
  static size_t deferIndex(const Expr& e);
  /**
   * True if e is an invocation of evaluation that can be purified, or
   * e does not have evaluation.
   */
  static bool isPure(const Expr& e);
  /**
   * True if e is in a legal final form, i.e. it needs no further normalization.
   * This is the case if e is pure and does not have deferred evaluation.
   */
  static bool isFinal(const Expr& e);
  /**
   * Given a term e, return a term that has no evaluation.
   * For each top-level evaluation term in e, we replace it by a fresh
   * parameter. We track a visited cache, and record new variables introduced in
   * this manner.
   */
  static Expr mkPurifyEvaluation(State& s,
                                 const Expr& e,
                                 ProgramOutCtx& ctx,
                                 std::vector<Expr>& newVars);
};

}  // namespace ethos

#endif /* FLATTEN_EVAL_H */
