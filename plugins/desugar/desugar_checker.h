/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef DESUGAR_CHECKER_H
#define DESUGAR_CHECKER_H

#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

class State;
class TypeChecker;
class Desugar;

/**
 */
class DesugarChecker : public StdPlugin
{
 public:
  DesugarChecker(State& s, Desugar* d);
  ~DesugarChecker();
  void finalizeRule(const Expr& v);

 private:
  void printTerm(const Expr& e, std::ostream& os);
  Expr d_true;
  Expr d_boolType;
  // parent desugar
  Desugar* d_desugar;
  // the rules
  std::stringstream d_rules;
  std::stringstream d_ruleInvokes;
};

}  // namespace ethos

#endif /* DESUGAR_CHECKER_H */
