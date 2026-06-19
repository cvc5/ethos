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
   * Check arity for kind, returns false if k cannot be applied to nargs.
   */
  static bool checkArity(Kind k, size_t nargs, std::ostream* out = nullptr);
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t);
  /**
   * Get type rule for literal kind k. The argument self is the expression to
   * instantiate eo::self with, if applicable, otherwise eo::? is used.
   * If no type rule has been set yet for k, the type rule for k is initialized
   * to a default, given by State::mkBuiltinType(k).
   */
  Expr getLiteralTypeRuleMaybeInit(Kind k, ExprValue* self = nullptr);
  /**
   * Evaluate the expression e in the given context.
   */
  Expr evaluate(ExprValue* e, Ctx& ctx);
  /**
   * Evaluate program app, where args[0] is a term of kind PROGRAM_CONST
   * and the remaining args are what is being applied to.
   *
   * If this returns (APPLY args), then the application does not
   * evaluate. This is the case if no case of the program matched, or
   * if an error was encountered.
   *
   * Otherwise, the program evaluates in one step to the returned term,
   * where the returned term is the result of evaluating the returned term
   * in the context that was matched.
   */
  Expr evaluateProgramApp(const std::vector<Expr>& args);
  /**
   * Evaluate literal op k applied to args. Returns (<k> args) if the
   * operator does not evaluate.
   */
  Expr evaluateLiteralOp(Kind k, const std::vector<ExprValue*>& args);
  /**
   * Return true iff e is closed, i.e. it has no free occurrences of variables
   * (Kind::VARIABLE). Occurrences of variables that are bound by an enclosing
   * application whose head is marked :binder do not count as free.
   */
  bool isClosed(ExprValue* e);
 private:
  /**
   * Helper for isClosed, where bound is the set of variables that are bound by
   * an enclosing binder. This checks whether e (and its subterms reachable
   * without crossing a further binder) has no free variables. It recurses only
   * when crossing a binder, so its recursion depth is bounded by the binder
   * nesting depth.
   */
  bool isClosedInternal(ExprValue* e, std::unordered_set<ExprValue*>& bound);
  /**
   * Helper for isClosedInternal, for an application of a binder (with attribute
   * a, either BINDER or LET_BINDER) whose head is head and whose arguments are
   * args (collected outermost first). Returns false if a free variable is found
   * in a body argument. Terms that should be checked in the current (outer)
   * scope, e.g. the bound terms of a let-binder, are appended to outerTerms.
   */
  bool isClosedBinder(Attr a,
                      ExprValue* head,
                      const std::vector<ExprValue*>& args,
                      std::unordered_set<ExprValue*>& bound,
                      std::vector<ExprValue*>& outerTerms);
  /** Collect the variables (Kind::VARIABLE) occurring as subterms of e. */
  void collectVariables(ExprValue* e, std::unordered_set<ExprValue*>& vars);
  /**
   * Match expression a with b. If this returns true, then ctx is a substitution
   * that when applied to b gives a. The substitution
   */
  static bool match(ExprValue* a, ExprValue* b, Ctx& ctx);
  /** Same as above, but takes a cache of pairs we have already visited */
  static bool match(ExprValue* a,
                    ExprValue* b,
                    Ctx& ctx,
                    std::set<std::pair<ExprValue*, ExprValue*>>& visited);
  /** */
  Expr getTypeAppInternal(std::vector<ExprValue*>& children,
                          Ctx& ctx,
                          std::ostream* out = nullptr);
  /** Are all args ground? */
  static bool isGround(const std::vector<ExprValue*>& args);
  /** Maybe evaluate */
  Expr evaluateProgramInternal(const std::vector<ExprValue*>& args,
                              Ctx& newCtx);
  /** Return its type */
  Expr getTypeInternal(ExprValue* e, std::ostream* out);
  /** Evaluate literal op */
  Expr evaluateLiteralOpInternal(Kind k, const std::vector<ExprValue*>& args);
  /** Evaluate nil
   * @param op The n-ary operator.
   * @param nil The nil terminator for the operator.
   * @param isLeft Whether we are :left-assoc-nil (or :right-assoc-nil).
   * @param tinst The reference type
   * @param tinstListArg If true, the reference type refers to the type of the
   * list. Otherwise, the reference type refers to the element type. This only
   * makes a difference for e.g. :right-assoc-nil operators whose type is
   * (-> T U U) where U != T.
   * @return The result of the evaluation.
   */
  Expr evaluateNil(ExprValue* op,
                   ExprValue* nil,
                   bool isLeft,
                   ExprValue* tinst,
                   bool tinstListArg = false);
  /** Evaluate list rev internal
   * @param op The n-ary operator.
   * @param nil The nil terminator for the operator.
   * @param isLeft Whether we are :left-assoc-nil (or :right-assoc-nil).
   * @param args The arguments to the application.
   * @return The result of the evaluation.
   */
  Expr evaluateListRevInternal(ExprValue* op,
                               ExprValue* nil,
                               bool isLeft,
                               const std::vector<ExprValue*>& args);
  /** Evaluate list erase internal
   * @param k The kind of application (ERASE or ERASE_ALL).
   * @param op The n-ary operator.
   * @param nil The nil terminator for the operator.
   * @param isLeft Whether we are :left-assoc-nil (or :right-assoc-nil).
   * @param args The arguments to the application.
   * @return The result of the evaluation.
   */
  Expr evaluateListEraseInternal(Kind k,
                                 ExprValue* op,
                                 ExprValue* nil,
                                 bool isLeft,
                                 const std::vector<ExprValue*>& args);
  /** Evaluate list setof internal
   * @param op The n-ary operator.
   * @param nil The nil terminator for the operator.
   * @param isLeft Whether we are :left-assoc-nil (or :right-assoc-nil).
   * @param args The arguments to the application.
   * @return The result of the evaluation.
   */
  Expr evaluateListSetOfInternal(ExprValue* op,
                                 ExprValue* nil,
                                 bool isLeft,
                                 const std::vector<ExprValue*>& args);
  /** Evaluate list multiset predicate internal
   * @param k The kind of application (MINCLUDE or MEQ).
   * @param op The n-ary operator.
   * @param nil The nil terminator for the operator.
   * @param isLeft Whether we are :left-assoc-nil (or :right-assoc-nil).
   * @param args The arguments to the application.
   * @return The result of the evaluation.
   */
  Expr evaluateListMPredInternal(Kind k,
                                 ExprValue* op,
                                 ExprValue* nil,
                                 bool isLeft,
                                 const std::vector<ExprValue*>& args);
  /** Evaluate list diff/intersection internal
   * @param k The kind of application (DIFF or INTER).
   * @param op The n-ary operator.
   * @param nil The nil terminator for the operator.
   * @param isLeft Whether we are :left-assoc-nil (or :right-assoc-nil).
   * @param args The arguments to the application.
   * @return The result of the evaluation.
   */
  Expr evaluateListDiffInterInternal(Kind k,
                                     ExprValue* op,
                                     ExprValue* nil,
                                     bool isLeft,
                                     const std::vector<ExprValue*>& args);
  /** Evaluate list singleton introduction internal
   * @param op The n-ary operator.
   * @param nil The nil terminator for the operator.
   * @param isLeft Whether we are :left-assoc-nil (or :right-assoc-nil).
   * @param args The arguments to the application.
   * @return The result of the evaluation.
   */
  Expr evaluateListSingletonIntroInternal(
      ExprValue* op,
      ExprValue* nil,
      bool isLeft,
      const std::vector<ExprValue*>& args);
  /**
   * Helper for above, starting with ret, append children in hargs to ret,
   * using n-ary operator op, which is :right-assoc-nil or :left-assoc-nil
   * if isLeft is true.
   * @param op The n-ary operator.
   * @param ret The current return value.
   * @param hargs The arguments to prepend to ret.
   * @param isLeft Whether we are :left-assoc-nil (or :right-assoc-nil).
   * @return The result of prepending the children.
   */
  Expr prependNAryChildren(ExprValue* op,
                           ExprValue* ret,
                           const std::vector<ExprValue*>& hargs,
                           bool isLeft);
  /** Type check */
  Expr getLiteralOpType(Kind k,
                        std::vector<ExprValue*>& children,
                        std::vector<ExprValue*>& childTypes,
                        std::ostream* out);
  /** Get the nil terminator */
  Expr computeConstructorTermInternal(AppInfo* ai,
                                      const std::vector<Expr>& children);
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
