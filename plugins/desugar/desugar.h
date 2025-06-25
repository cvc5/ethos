/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef DESUGAR_H
#define DESUGAR_H

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

/**
 */
class Desugar : public Plugin
{
 public:
  Desugar(State& s);
  ~Desugar();
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
  void printName(const Expr& e, std::ostream& os);
  void printTerm(const Expr& e, std::ostream& os);
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
  void finalizeSetLiteralTypeRule(Kind k, const Expr& t);
  void finalizeProgram(const Expr& v, const Expr& prog);
  void finalizeDefinition(const std::string& name, const Expr& t);
  void finalizeDeclaration(const Expr& t);
  void finalizeRule(const Expr& v);
  void finalizeDatatype(const Expr& d);
  /** */
  Expr mkSanitize(const Expr& t);
  Expr mkSanitize(const Expr& t,
                  std::map<Expr, Expr>& visited,
                  size_t& varCount,
                  bool inPatMatch,
                  std::vector<std::pair<Expr, Expr>>& newVars);
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  /** Declares seen */
  std::vector<std::pair<Expr, Kind>> d_declSeen;
  /** Attributes marked */
  std::map<Expr, std::pair<Attr, Expr>> d_attrDecl;
  /** Declares processed */
  std::set<Expr> d_declProcessed;
  /** Handles overloading */
  std::map<std::string, size_t> d_overloadCount;
  /** */
  std::map<Expr, size_t> d_overloadId;
  /** */
  std::map<Expr, Expr> d_overloadSanVisited;
  /** Common constants */
  Expr d_any;
  Expr d_null;
  Expr d_listNil;
  Expr d_listCons;
  Expr d_listType;
  /** Are we generating programs that are VC targets */
  bool d_genVcs;

  std::stringstream d_numDecl;
  std::stringstream d_num;
  std::stringstream d_defs;
  std::stringstream d_eoNilNground;
  std::stringstream d_eoNil;
  std::stringstream d_eoTypeofParam;
  std::stringstream d_eoTypeof;
  std::stringstream d_eoTypeofNGround;
  std::stringstream d_eoDtNGround;
  std::stringstream d_eoDtCons;
  std::stringstream d_eoDtSel;
  std::stringstream d_eoRules;

  /** term we have pattern matched on for typeof */
  std::vector<Expr> d_typeOfVars;
  /** variable counter for typeof */
  size_t d_typeOfVarCount;
};

}  // namespace ethos

#endif /* COMPILER_H */
