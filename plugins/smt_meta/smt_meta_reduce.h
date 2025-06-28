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

#include "expr_info.h"
#include "expr_trie.h"
#include "plugin.h"
#include "type_checker.h"

namespace ethos {

class State;
class TypeChecker;

class SelectorCtx
{
 public:
  SelectorCtx() {}
  /*
  SelectorCtx() : d_counter(0) {}
  std::string push(const std::string& next)
  {
    d_counter++;
    std::stringstream ss;
    ss << "z" << d_counter;
    d_letBegin << "(let ((z" << d_counter << " " << next << ")) ";
    d_letEnd << ")";
    return ss.str();
  }
  */
  std::map<Expr, std::string> d_ctx;
  // std::stringstream d_letBegin;
  // std::stringstream d_letEnd;
  // size_t d_counter;
};

/**
 */
class SmtMetaReduce : public Plugin
{
 public:
  SmtMetaReduce(State& s);
  ~SmtMetaReduce();
  /** */
  void bind(const std::string& name, const Expr& e) override;
  /** Mark attributes */
  void markConstructorKind(const Expr& v, Attr a, const Expr& cons) override;
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Finalize */
  void finalize() override;

  /**
   */
  bool echo(const std::string& msg) override;

 private:
  void printConjunction(size_t n,
                        const std::string& conj,
                        std::ostream& os,
                        const SelectorCtx& ctx);
  bool printEmbPatternMatch(const Expr& c,
                            const std::string& initCtx,
                            std::ostream& os,
                            SelectorCtx& ctx,
                            size_t& nconj);
  bool printEmbAtomicTerm(const Expr& c, std::ostream& os);
  bool printEmbTerm(const Expr& c, std::ostream& os, const SelectorCtx& ctx);
  void finalizePrograms();
  void finalizeProgram(const Expr& v, const Expr& prog);
  void finalizeDeclarations();
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  /** is smt apply term */
  bool isSmtApplyTerm(const Expr& t,
                      std::string& name,
                      std::vector<Expr>& args);
  bool isSmtApplyTerm(const Expr& t);
  /** is smt apply, return the arity */
  size_t isSmtApply(const Expr& t);
  /** is smt term type */
  bool isSmtTermType(const Expr& t);
  /** is smt to eo */
  bool isSmtToEo(const Expr& t);
  /** is smt to eo */
  bool isEoToSmt(const Expr& t);
  /** is internal symbol? */
  bool isInternalSymbol(const Expr& t);
  /** get kind for suffix */
  Kind getKindForSuffix(const std::string& suf) const;
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** Declares seen */
  std::set<Expr> d_declSeen;
  /** Program declarations processed */
  std::set<Expr> d_progDeclProcessed;
  /** Programs seen */
  std::vector<std::pair<Expr, Expr>> d_progSeen;
  /** Attributes marked */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  /** Mapping expressions to strings */
  std::map<Expr, std::string> d_embMapAtomic;
  /** Common constants */
  Expr d_null;
  /** Number of current scopes. Bindings at scope>0 are not remembered */
  size_t d_nscopes;
  std::stringstream d_termDecl;
  std::stringstream d_eoTermDecl;
  std::stringstream d_defs;
  std::stringstream d_rules;
  std::stringstream d_smtVc;
  std::map<std::string, Kind> d_sufToKind;
  /** SMT-LIB indexed operators */
  std::map<std::string, size_t> d_indexedOperators;
  // SMT-LIB symbols
  bool d_inInitialize;
};

}  // namespace ethos

#endif /* COMPILER_H */
