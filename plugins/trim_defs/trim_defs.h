/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef TRIM_DEFS_H
#define TRIM_DEFS_H

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

class TrimList
{
 public:
  TrimList(State& s, const std::map<Expr, std::pair<Attr, Expr>>& attrDecl);
  std::vector<std::pair<Expr, Expr>> getTrimList(const std::vector<Expr>& es);
  std::vector<std::pair<Expr, Expr>> getTrimList(const std::vector<Expr>& es,
                                                 std::map<Expr, bool>& visited);

 private:
  Expr d_null;
  State& d_state;
  /** Attributes marked */
  const std::map<Expr, std::pair<Attr, Expr>>& d_attrDecl;
};

/**
 */
class TrimDefs : public Plugin
{
  friend class TypeChecker;

 public:
  TrimDefs(State& s);
  ~TrimDefs();
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

 private:
  void printTerm(const Expr& t, std::ostream& os);
  void printParamList(const std::vector<Expr>& vars,
                      std::ostream& os,
                      std::vector<Expr>& params,
                      bool useImplicit);
  void printParamList(const std::vector<Expr>& vars,
                      std::ostream& os,
                      std::vector<Expr>& params,
                      bool useImplicit,
                      std::map<Expr, bool>& visited,
                      bool& firstParam,
                      bool isOpaque = false);
  void printSetLiteralTypeRule(Kind k, const Expr& t);
  void printProgram(const Expr& v, const Expr& prog);
  void printDefinition(const std::string& name, const Expr& t);
  void printDeclaration(const Expr& t);
  void printRule(const Expr& v);
  void printDatatype(const Expr& d);
  std::map<Kind, Expr> d_litTypeRule;
  std::vector<Kind> d_litTypeRuleList;
  /** Attributes marked */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  Expr d_null;
  std::stringstream d_defs;
  std::string d_defTarget;
  bool d_setDefTarget;
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
};

}  // namespace ethos

#endif /* COMPILER_H */
