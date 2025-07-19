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

class ProgramOutCtx
{
 public:
  ProgramOutCtx(State& s, size_t pcount);
  void pushArg(const Expr& a);
  void pushArgTyped(const Expr& a, const Expr& at);
  void popArg();
  Expr allocateVariable(const Expr& retType);
  Expr allocateProgram(const std::vector<Expr>& nvars, const std::vector<Expr>& nargs, const Expr& ret);
  std::vector<Expr> getArgs() { return d_args; }
  std::map<Expr, Expr> d_visited;

 private:
  Expr ensureFinalArg(const Expr& e);
  Expr allocateProgramInternal(const Expr& retType);
  Expr mkCurrentProgramPat(const Expr& prog);
  Expr getTypeInternal(const Expr& e);
  State& d_state;
  std::vector<Expr> d_args;
  std::vector<Expr> d_argTypes;
  std::string d_progPrefix;
  size_t d_varCount;
  size_t d_progCount;
  std::vector<std::pair<Expr, Expr>> d_progAlloc;
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
   * Flattens the evaluation in the body of a case of the definition of program
   * v. Prints the returned term equivalent to caseBody on os. Introduces
   * auxiliary programs to do so, printed on osp.
   */
  static Expr flattenEval(State& s,
                          ProgramOutCtx& ctx,
                          const Expr& pat,
                          const Expr& body);
  static Expr flattenEval(State& s,
                          ProgramOutCtx& ctx,
                          const Expr& t);
  static Expr flattenEvalInternal(State& s,
                                  ProgramOutCtx& ctx,
                                  const Expr& t);
  /**
   * True if this is an invocation of evaluation that can be purified.
   */
  static bool isPure(const Expr& e);
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
