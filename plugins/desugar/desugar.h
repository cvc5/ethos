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

#include "../std_plugin.h"

namespace ethos {

class State;
class TypeChecker;

/**
 */
class Desugar : public StdPlugin
{
 public:
  Desugar(State& s);
  ~Desugar();
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
  void printName(const Expr& e, std::ostream& os);
  void printTerm(const Expr& e, std::ostream& os);
  void printParamList(const std::vector<Expr>& vars,
                      std::ostream& os,
                      bool useImplicit,
                      bool isOpaque = false);
  void printParamList(const std::vector<Expr>& vars,
                      std::ostream& os,
                      std::vector<Expr>& params,
                      std::map<Expr, bool>& visited,
                      bool useImplicit,
                      bool isOpaque = false);
  void getParamList(const std::vector<Expr>& vars,
                    std::vector<Expr>& params,
                    std::map<Expr, bool>& visited);
  void finalizeParamList(std::ostream& os,
                         const std::vector<Expr>& params,
                         bool useImplicit,
                         const std::vector<Expr>& nimplicit,
                         bool isOpaque = false,
                         size_t startIndex = 0);
  void finalizeProgram(const Expr& v, const Expr& prog, std::ostream& os);
  void finalizeDefinition(const std::string& name, const Expr& t);
  void finalizeDeclaration(const Expr& t, std::ostream& os) override;
  void finalizeRule(const Expr& v);
  /**
   * Finalize datatype or datatype constructor.
   */
  void finalizeDatatype(const Expr& d, Attr a, const Expr& attrCons);
  void finalizeWellFounded();
  /** */
  Expr mkSanitize(const Expr& t);
  Expr mkSanitize(const Expr& t,
                  std::map<Expr, Expr>& visited,
                  size_t& varCount,
                  bool inPatMatch,
                  std::vector<std::pair<Expr, Expr>>& newVars);
  Expr mkRequiresModelSat(bool tgt, const Expr& test, const Expr& ret);
  Expr mkRequiresModelTypeofBool(const Expr& test, const Expr& ret);
  Expr mkRequiresModelIsSmtTerm(const Expr& test, const Expr& ret);
  Expr mkRequiresEq(const Expr& t1, const Expr& t2, const Expr& ret, bool negated=false);
  Attr getAttribute(const Expr& e);
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
  Expr d_null;
  Expr d_listNil;
  Expr d_listCons;
  Expr d_listType;
  Expr d_boolType;
  /** Are we generating programs that are VC targets */
  bool d_genVcs;

  std::stringstream d_defs;
  std::stringstream d_eoNilNground;
  std::stringstream d_eoNil;
  std::stringstream d_eoTypeof;
  std::stringstream d_eoTypeofNGround;
  std::stringstream d_eoDtConsParam;
  std::stringstream d_eoDtCons;
  std::stringstream d_eoDtSel;
  std::stringstream d_eoVc;
  std::stringstream d_eoVcWf;
  // for model semantics
  std::stringstream d_eoModelEval;
  std::stringstream d_eoModelConstPred;

  Expr d_peoModelSat;
  Expr d_peoModelTypeof;
  Expr d_peoModelIsSmtTerm;
  Expr d_peoRequiresEq;
  Expr d_peoRequiresDeq;
  size_t d_eoDtConsParamCount;
  bool d_genWfCond;
};

}  // namespace ethos

#endif /* DESUGAR_H */
