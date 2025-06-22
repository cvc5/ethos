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

#include "plugin.h"
#include "expr_info.h"
#include "expr_trie.h"
#include "type_checker.h"

namespace ethos {

class State;
class TypeChecker;

/**
 */
class SmtMetaReduce : public Plugin
{
  friend class TypeChecker;
public:
  SmtMetaReduce(State& s);
  ~SmtMetaReduce();
  /** Reset */
  void reset() override;
  /** Push scope */
  void pushScope() override;
  /** Pop scope */
  void popScope() override;
  /** include file, if not already done */
  void includeFile(const Filepath& s, bool isReference, const Expr& referenceNf) override;
  /** Set type rule for literal kind k to t */
  void setLiteralTypeRule(Kind k, const Expr& t) override;
  /** */
  void bind(const std::string& name, const Expr& e) override;
  /** Mark attributes */
  void markConstructorKind(const Expr& v, Attr a, const Expr& cons) override;
  /** Mark oracle command */
  void markOracleCmd(const Expr& v, const std::string& ocmd) override;
  /** Define program */
  void defineProgram(const Expr& v, const Expr& prog) override;
  /** Finalize */
  void finalize() override;
  /** To string, which returns the smt2 formalization of the meta-level correctness of the signature */
  std::string toString();
private:
  void printConjunction(size_t n, const std::string& conj, std::ostream& os);
  bool printEmbPatternMatch(const Expr& c, const std::string& initCtx, std::ostream& os, std::map<Expr, std::string>& ctx, size_t& nconj);
  bool printEmbAtomicTerm(const Expr& c, std::ostream& os);
  bool printEmbTerm(const Expr& c, std::ostream& os, const std::map<Expr, std::string>& ctx, bool ignorePf = false);
  void finalizeDeclarations();
  void finalizeRules();
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** Declares processed */
  std::set<Expr> d_declSeen;
  /** Rules processed */
  std::set<Expr> d_ruleSeen;
  /** Attributes marked */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  /** Common constants */
  Expr d_listNil;
  Expr d_listCons;
  Expr d_listType;
  /** Number of current scopes. Bindings at scope>0 are not remembered */
  size_t d_nscopes;
  std::stringstream d_termDecl;
  std::stringstream d_termDeclEnd;
  std::stringstream d_defs;
  std::stringstream d_rules;
  std::stringstream d_eval;

  std::stringstream d_eoNilVarList;
  std::stringstream d_eoNil;
  std::stringstream d_eoTypeof;
  std::stringstream d_eoDtSelectors;
  std::stringstream d_eoDtConstructors;
  std::stringstream d_hasProofList;
};

}  // namespace ethos

#endif /* COMPILER_H */
