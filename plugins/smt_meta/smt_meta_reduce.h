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
  std::map<Expr, std::string> d_ctx;
  std::stringstream d_letBegin;
  std::stringstream d_letEnd;
  size_t d_counter;
};

/**
 */
class SmtMetaReduce : public Plugin
{
 public:
  SmtMetaReduce(State& s);
  ~SmtMetaReduce();
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t) override;
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
  bool printEmbTerm(const Expr& c,
                    std::ostream& os,
                    const SelectorCtx& ctx,
                    bool ignorePf = false);
  void finalizePrograms();
  void finalizeProgram(const Expr& v, const Expr& prog);
  void finalizeDeclarations();
  void finalizeRule(const Expr& v);
  void finalizeRules();
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  /** is smt apply term */
  bool isSmtApplyTerm(const Expr& t, std::string& name, std::vector<Expr>& args);
  /** is smt apply, return the arity */
  size_t isSmtApply(const Expr& t, std::string& name);
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** Declares seen */
  std::set<Expr> d_declSeen;
  /** Rules seen */
  std::set<Expr> d_ruleSeen;
  /** Program declarations processed */
  std::set<Expr> d_progDeclProcessed;
  /** Programs seen */
  std::vector<std::pair<Expr, Expr>> d_progSeen;
  /** Attributes marked */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  /** Handles overloading */
  std::map<std::string, size_t> d_overloadCount;
  /** */
  std::map<Expr, size_t> d_overloadId;
  /** Mapping expressions to strings */
  std::map<Expr, std::string> d_embMapAtomic;
  /** */
  Expr d_eoTmpInt;
  Expr d_eoTmpNil;
  /** Common constants */
  Expr d_null;
  Expr d_listNil;
  Expr d_listCons;
  Expr d_listType;
  /** Number of current scopes. Bindings at scope>0 are not remembered */
  size_t d_nscopes;
  std::stringstream d_termDecl;
  std::stringstream d_defs;
  std::stringstream d_rules;
  std::stringstream d_eoTypeofLit;
  std::stringstream d_eoTypeofEnd;
  std::stringstream d_smtVc;
  // SMT-LIB symbols
  bool d_inInitialize;
};

}  // namespace ethos

#endif /* COMPILER_H */
