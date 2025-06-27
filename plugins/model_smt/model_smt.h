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
  /** the state */
  State& d_state;
  /** the type checker */
  TypeChecker& d_tc;
  void addSmtLibSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    Kind ret);
  void printSmtType(const std::string& name, std::vector<Kind>& args);
  void printSmtTerm(const std::string& name, std::vector<Kind>& args, Kind ret);
  std::map<Kind, Expr> d_kindToType;
  std::map<Kind, std::string> d_kindToEoPrefix;
  std::map<std::string, std::string> d_overloadRevert;
  /** SMT-LIB indexed operators */
  std::map<std::string, size_t> d_indexedOperators;
  std::stringstream d_eval;
  std::stringstream d_typeEnum;
  std::stringstream d_isValue;
  // SMT-LIB symbols
  std::map<std::string, std::pair<std::vector<Kind>, Kind>> d_smtLibSyms;
};

}  // namespace ethos

#endif /* COMPILER_H */
