/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef SMT_META_REDUCE_H
#define SMT_META_REDUCE_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

class State;
class TypeChecker;

class ConjPrint
{
 public:
  ConjPrint();
  void push(const std::string& str);
  void printConjunction(std::ostream& os, bool isDisj = false);
  std::stringstream d_ss;
  size_t d_npush;
};

/**
 * The datatype we are at.
 */
enum class MetaKind
{
  /** A context in which the deep embedding of the term is a Eunoia term */
  EUNOIA,
  /** A context in which the deep embedding of the term is an SMT-LIB term */
  SMT,
  /** A context in which the deep embedding of the term is an SMT-LIB type */
  SMT_TYPE,
  /** A context in which the deep embedding of the term is an SMT-LIB value */
  SMT_VALUE,
  /** A context in which the deep embedding of the term is an SMT-LIB map value
   */
  SMT_MAP,
  /** A builtin SMT-LIB term context */
  SMT_BUILTIN,
  /** A program */
  PROGRAM,
  /** No context */
  NONE
};
std::string metaKindToString(MetaKind k);
std::string metaKindToPrefix(MetaKind k);
std::string metaKindToCons(MetaKind k);

class SelectorCtx
{
 public:
  SelectorCtx();
  void clear();
  /**
   * Maps parameters to a string representation of what
   * that parameter was mapped to. This is a chain of
   * datatype selectors, where we do not model the AST
   * of this chain.
   */
  std::map<Expr, std::string> d_ctx;
  /** The context it was matched in */
  std::map<Expr, MetaKind> d_tctx;
};

/**
 */
class SmtMetaReduce : public StdPlugin
{
 public:
  SmtMetaReduce(State& s);
  ~SmtMetaReduce();
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Finalize */
  void finalize() override;
  /**
   */
  bool echo(const std::string& msg) override;

  static bool printMetaType(const Expr& t,
                            std::ostream& os,
                            MetaKind tctx = MetaKind::NONE);
  /** Get the name of expression e, expected to be an atomic term */
  static std::string getName(const Expr& e);
  /** Is e a datatype constructor embedding? */
  static bool isEmbedCons(const Expr& e);
  /**
   * Return the "meta-kind" of a type typ, based on its naming convention
   * introduced in the model_smt layer. In other words, we return the datatype
   * that typ represents if applicable, SMT_BUILTIN if typ refers to a builtin
   * SMT-LIB type, or elseKind otherwise.
   * @param typ The given type.
   * @param elseKind The returned kind if typ does not have a special meaning.
   * @return The meta-kind of typ, or elseKind otherwise.
   */
  static MetaKind getTypeMetaKind(const Expr& typ,
                                  MetaKind elseKind = MetaKind::EUNOIA);
  /**
   * Get the meta kind of the type of expression e, or else kind otherwise.
   * In other words, we return the datatype that e is a constructor of in the
   * final embedding, SMT_BUILTIN if e is a builtin SMT-LIB application, or
   * elseKind otherwise.
   * @param s Reference to the state
   * @param e The given expression.
   * @param cname Updated to the root name of the constructor.
   * @return The meta-kind of the type of e, or elseKind otherwise.
   */
  static MetaKind getMetaKind(State& s, const Expr& e, std::string& cname);

 private:
  bool printEmbPatternMatch(const Expr& c,
                            const std::string& initCtx,
                            std::ostream& os,
                            SelectorCtx& ctx,
                            ConjPrint& print,
                            MetaKind tinit = MetaKind::NONE);
  void printEmbAtomicTerm(const Expr& c,
                          std::ostream& os,
                          MetaKind tctx = MetaKind::NONE);
  bool printEmbTerm(const Expr& c,
                    std::ostream& os,
                    const SelectorCtx& ctx,
                    MetaKind tinit = MetaKind::NONE);
  void finalizePrograms();
  void finalizeProgram(const Expr& v, const Expr& prog);
  static bool isProgram(const Expr& t);
  static bool isSmtApplyApp(const Expr& oApp);
  static std::string getEmbedName(const Expr& oApp);
  /** Program declarations processed */
  std::set<Expr> d_progDeclProcessed;
  /** Programs seen */
  std::vector<std::pair<Expr, Expr>> d_progSeen;
  /** Common constants */
  Expr d_null;
  std::stringstream d_defs;
  std::stringstream d_rules;
  std::stringstream d_smtVc;
  /** */
  std::map<std::pair<Expr, size_t>, MetaKind> d_metaKindArg;
  /** */
  bool isSmtLibExpression(MetaKind ctx);
  /**
   */
  bool isProgramApp(const Expr& app);
  /**
   * This returns the expected meta-kind for the i^th child of
   * parent. It should not depend on parent[i] at all.
   */
  MetaKind getMetaKindArg(const Expr& parent, size_t i, MetaKind parentCtx);
  /**
   * Returns the result of calling the above method for all
   * children i of parent.
   */
  std::vector<MetaKind> getMetaKindArgs(const Expr& parent, MetaKind parentCtx);
  /**
   * Get the meta-kind returned by a child.
   */
  MetaKind getMetaKindReturn(const Expr& child, MetaKind parentCtx);
  /**
   * Same as above, but collects (flattens) the arguments of APPLY
   */
  MetaKind getMetaKindReturn(const Expr& child,
                             std::vector<Expr>& appArgs,
                             MetaKind parentCtx);
};

}  // namespace ethos

#endif /* COMPILER_H */
