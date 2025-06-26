/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef SMT_MODEL_H
#define SMT_MODEL_H

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
 * Used to generate a *.eo file that defines SMT-LIB model semantics.
 */
class ModelSmt : public Plugin
{
 public:
  ModelSmt(State& s);
  ~ModelSmt();
  /** */
  void bind(const std::string& name, const Expr& e) override;
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
  void finalizeDeclaration(const Expr& t, std::ostream& os);
  void finalizeRule(const Expr& v);
  void finalizeDatatype(const Expr& d);
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  std::vector<Expr> d_evalParams;
  std::vector<Expr> d_typeEnumParams;
  void addSmtLibSym(const std::string& sym, const std::vector<Kind>& args, Kind ret);
  void printSmtType(const std::string& name, std::vector<Kind>& args);
  void printSmtTerm(const std::string& name, std::vector<Kind>& args, Kind ret);
  std::stringstream d_evalParam;
  std::stringstream d_evalNGround;
  std::stringstream d_eval;
  std::stringstream d_typeEnumParam;
  std::stringstream d_typeEnumNGround;
  std::stringstream d_typeEnum;
  // SMT-LIB symbols
  std::map<std::string, std::pair<std::vector<Kind>, Kind>> d_smtLibSyms;
};

}  // namespace ethos

#endif /* COMPILER_H */
