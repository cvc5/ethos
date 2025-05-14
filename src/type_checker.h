/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef TYPE_CHECKER_H
#define TYPE_CHECKER_H

#include <map>
#include <set>
#include "expr.h"
#include "expr_trie.h"
#include "expr_info.h"

namespace ethos {

class State;
class Stats;
class Options;
class Plugin;

/** 
 * The type checker for Ethos. The main algorithms it implements are
 * getType, match, and evaluate.
 */
class TypeChecker
{
  friend class State;

 public:
  TypeChecker(State& s, Options& opts);
  ~TypeChecker();
  /**
   * Return the type of expression e. This returns nullptr if e
   * is not well-typed. In this case, an error message is written on
   * out if it is provided.
   */
  Expr getType(Expr& e, std::ostream* out = nullptr);
  /**
   * Get the type of an application, equivalent to calling getType on
   * (APPLY children).
   */
  Expr getTypeApp(std::vector<Expr>& children, std::ostream* out = nullptr);
  /**
   * Check arity for kind, returns false if k cannot be applied to nargs.
   */
  static bool checkArity(Kind k, size_t nargs, std::ostream* out = nullptr);
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t);
  /**
   * Evaluate the expression e in the given context.
   */
  Expr evaluate(ExprValue* e, Ctx& ctx);
  /**
   * Evaluate program, where args[0] is a term of kind PROGRAM_CONST or ORACLE
   * and the remaining args are what is being applied to.
   *
   * If this returns (APPLY args), then the application does not
   * evaluate. This is the case if no case of the program matched, or
   * if an error was encountered.
   *
   * Otherwise, the program evaluates in one step to the returned term,
   * and is equal to the result of evaluating that expression in the context newCtx,
   * which is computed in this call.
   *
   * If we are evaluating an oracle, newCtx is never set and the returned term
   * is the result of calling the oracle and parsing its output.
   */
  Expr evaluateProgram(const std::vector<ExprValue*>& args,
                       Ctx& newCtx);
  /**
   * Evaluate literal op k applied to args. Returns (<k> args) if the
   * operator does not evaluate.
   */
  Expr evaluateLiteralOp(Kind k, const std::vector<ExprValue*>& args);
 private:
  /**
   * Match expression a with b. If this returns true, then ctx is a substitution
   * that when applied to b gives a. The substitution
   */
  bool match(ExprValue* a, ExprValue* b, Ctx& ctx);
  /** Same as above, but takes a cache of pairs we have already visited */
  bool match(ExprValue* a,
             ExprValue* b,
             Ctx& ctx,
             std::set<std::pair<ExprValue*, ExprValue*>>& visited);
  /** */
  Expr getTypeAppInternal(std::vector<ExprValue*>& children,
                          Ctx& ctx,
                          std::ostream* out = nullptr);
  /** Compute the union of flags of terms in args */
  static char getFlags(const std::vector<ExprValue*>& args);
  /** Are all args ground? */
  static bool isGround(const std::vector<ExprValue*>& args);
  /** Maybe evaluate */
  Expr evaluateProgramInternal(const std::vector<ExprValue*>& args,
                              Ctx& newCtx);
  /** Return its type */
  Expr getTypeInternal(ExprValue* e, std::ostream* out);
  /** 
   * Get or set type rule (to default) for literal kind k. The argument
   * self is the expression to instantiate eo::self with, if applicable,
   * otherwise eo::? is used.
   */
  Expr getOrSetLiteralTypeRule(Kind k, ExprValue * self = nullptr);
  /** Evaluate literal op */
  Expr evaluateLiteralOpInternal(Kind k, const std::vector<ExprValue*>& args);
  /** Type check */
  Expr getLiteralOpType(Kind k,
                              std::vector<ExprValue*>& children,
                              std::vector<ExprValue*>& childTypes,
                              std::ostream* out);
  /** Get the nil terminator */
  Expr computeConstructorTermInternal(AppInfo* ai,
                                      const std::vector<Expr>& children);
  /** Returns the (possibly disambiguated) operator in children and its nil terminator */
  bool computedParameterizedInternal(AppInfo* ai,
                                     const std::vector<Expr>& children,
                                     Expr& hd,
                                     Expr& nil);
  /** The state */
  State& d_state;
  /** Plugin of the state */
  Plugin * d_plugin;
  /** Mapping literal kinds to type rules */
  std::map<Kind, Expr> d_literalTypeRules;
  /** The null expression */
  Expr d_null;
  Expr d_negOne;
  /** Stats enabled? */
  bool d_statsEnabled;
  /** Reference to the stats */
  Stats& d_sts;
};

}  // namespace ethos

#endif 
