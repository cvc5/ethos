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
class Desugar : public Plugin
{
  friend class TypeChecker;
public:
  Desugar(State& s);
  ~Desugar();
  /** Intialize */
  void initialize() override;
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
  void printConjunction(size_t n, const std::string& conj, std::ostream& os, const SelectorCtx& ctx);
  bool printEmbPatternMatch(const Expr& c, const std::string& initCtx, std::ostream& os, SelectorCtx& ctx, size_t& nconj);
  bool printEmbAtomicTerm(const Expr& c, std::ostream& os);
  bool printEmbTerm(const Expr& c, std::ostream& os, const SelectorCtx& ctx, bool ignorePf = false);
  void finalizePrograms();
  void finalizeProgram(const Expr& v, const Expr& prog);
  void finalizeDeclarations();
  void finalizeRule(const Expr& v);
  void finalizeRules();
  /** Does t have subterm s? */
  static bool hasSubterm(const Expr& t, const Expr& s);
  /** Terms with kind */
  //static std::vector<Expr> getSubtermsWithKind(const Expr& t, Kind k);
  /** */
  Expr mkRemoveAnnotParam(const Expr& t, std::vector<Expr>& vars);
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** Declares seen */
  std::vector<std::pair<Expr, Kind>> d_declSeen;
  /** Declares processed */
  std::set<Expr> d_declProcessed;
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

  std::stringstream d_numDecl;
  std::stringstream d_num;
  std::stringstream d_defs;
  std::stringstream d_eoNil;
  std::stringstream d_eoNilParam;
  std::stringstream d_eoTypeof;
  std::stringstream d_eoTypeofParam;
  std::stringstream d_eoDtCons;
  std::stringstream d_eoDtConsParam;
  std::stringstream d_eoDtSel;
  std::stringstream d_eoDtSelParam;
  bool d_inInitialize;
};

}  // namespace ethos

#endif /* COMPILER_H */
