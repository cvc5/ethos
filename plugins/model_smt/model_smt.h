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
#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

/**
 * Used to generate a *.eo file that defines SMT-LIB model semantics.
 */
class ModelSmt : public StdPlugin
{
 public:
  ModelSmt(State& s);
  ~ModelSmt();
  /** */
  void bind(const std::string& name, const Expr& e) override;
  /** Finalize */
  void finalize() override;

 private:
  void addSmtLibSym(const std::string& sym,
                    const std::vector<Kind>& args,
                    Kind ret);
  void printSmtType(const std::string& name, std::vector<Kind>& args);
  void printSmtTerm(const std::string& name, std::vector<Kind>& args, Kind ret);
  std::map<Kind, Expr> d_kindToType;
  std::map<Kind, std::string> d_kindToEoPrefix;
  std::map<Kind, std::string> d_kindToEoCons;
  std::map<std::string, std::string> d_overloadRevert;
  std::stringstream d_customEval;
  std::stringstream d_isValue;
  std::stringstream d_isType;
  std::stringstream d_typeEnum;
  std::stringstream d_constPred;
  // SMT-LIB term embedding
  std::stringstream d_embedTypeDt;
  std::stringstream d_embedTermDt;
  std::stringstream d_embedEoTermDt;
  // SMT-LIB standard evaluation
  std::stringstream d_eval;
  // SMT-LIB symbols
  std::map<std::string, std::pair<std::vector<Kind>, Kind>> d_smtLibSyms;
};

}  // namespace ethos

#endif /* COMPILER_H */
