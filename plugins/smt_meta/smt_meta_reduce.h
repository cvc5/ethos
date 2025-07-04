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
enum class TermContextKind
{
  /** A context in which the deep embedding of the term is a Eunoia term */
  EUNOIA,
  /** A context in which the deep embedding of the term is an SMT-LIB term */
  SMT,
  /** A context in which the deep embedding of the term is an SMT-LIB type */
  SMT_TYPE,
  /** A context in which the deep embedding of the term is an SMT-LIB value */
  SMT_VALUE,
  /**
   * These are variants of the above, used for exception handling on the
   * model_smt layer. In particular, the use of an eo.Term datatype selector
   * must ensure that it is properly applied. Otherwise we are introducing
   * *incomplete* behavior in the final SMT encoding, which leads to
   * unsoundness at the meta-level.
   *
   * We assign a "_GUARDED" kind for the datatype selectors for the types
   * corresponding to extracting the an SMT-LIB expression from a deep
   * embedding of a Eunoia term. It is critical for soundness that these are
   * *only* used when exception handling is done soundly, namely by guarding
   * with eo::is_ok.
   *
   * This form of exception handling is all done in a *single* place in
   * model_smt.eo, for each type. See the methods $smt_try_X.
   */
  SMT_GUARDED,
  SMT_TYPE_GUARDED,
  SMT_VALUE_GUARDED,
  /** A builtin SMT-LIB term context */
  SMT_BUILTIN,
  /** A program */
  PROGRAM,
  /** No context */
  NONE
};
std::string termContextKindToString(TermContextKind k);
std::string termContextKindToPrefix(TermContextKind k);
std::string termContextKindToCons(TermContextKind k);

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
  std::map<Expr, TermContextKind> d_tctx;
};

/**
 */
class SmtMetaReduce : public StdPlugin
{
 public:
  SmtMetaReduce(State& s);
  ~SmtMetaReduce();
  /** */
  void bind(const std::string& name, const Expr& e) override;
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Finalize */
  void finalize() override;
  /**
   */
  bool echo(const std::string& msg) override;

 private:
  bool printEmbPatternMatch(const Expr& c,
                            const std::string& initCtx,
                            std::ostream& os,
                            SelectorCtx& ctx,
                            ConjPrint& print,
                            TermContextKind tinit = TermContextKind::NONE);
  void printEmbAtomicTerm(const Expr& c,
                          std::ostream& os,
                          TermContextKind tctx = TermContextKind::NONE);
  void printEmbType(const Expr& c,
                    std::ostream& os,
                    TermContextKind tctx = TermContextKind::NONE);
  bool printEmbTerm(const Expr& c,
                    std::ostream& os,
                    const SelectorCtx& ctx,
                    TermContextKind tinit = TermContextKind::NONE);
  void finalizePrograms();
  void finalizeProgram(const Expr& v, const Expr& prog);
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  bool isProgram(const Expr& t);
  std::string getName(const Expr& e);
  std::string getEmbedName(const Expr& oApp);
  /** Program declarations processed */
  std::set<Expr> d_progDeclProcessed;
  /** Programs seen */
  std::vector<std::pair<Expr, Expr>> d_progSeen;
  /** Attributes marked */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  /** Common constants */
  Expr d_null;
  std::stringstream d_defs;
  std::stringstream d_rules;
  std::stringstream d_smtVc;
  /** The Eunoia program that returns the meta-kind of terms */
  Expr d_eoGetMetaKind;
  /** */
  std::map<std::pair<Expr, size_t>, TermContextKind> d_metaKindArg;
  /** */
  bool isSmtLibExpression(TermContextKind ctx);
  /**
   */
  TermContextKind getTypeMetaKind(const Expr& typ, TermContextKind elseKind=TermContextKind::EUNOIA);
  /**
   */
  bool isProgramApp(const Expr& app);
  /**
   * This returns the expected meta-kind for the i^th child of
   * parent. It should not depend on parent[i] at all.
   */
  TermContextKind getMetaKindArg(const Expr& parent,
                                 size_t i,
                                 TermContextKind parentCtx);
  /**
   * Returns the result of calling the above method for all
   * children i of parent.
   */
  std::vector<TermContextKind> getMetaKindArgs(const Expr& parent,
                                               TermContextKind parentCtx);
  /**
   * Get the meta-kind returned by a child.
   */
  TermContextKind getMetaKindReturn(const Expr& child,
                                    TermContextKind parentCtx);
  /**
   * Same as above, but collects (flattens) the arguments of APPLY
   */
  TermContextKind getMetaKindReturn(const Expr& child,
                                    std::vector<Expr>& appArgs,
                                    TermContextKind parentCtx);
};

}  // namespace ethos

#endif /* COMPILER_H */
