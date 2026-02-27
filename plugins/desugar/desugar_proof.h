/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef DESUGAR_PROOF_H
#define DESUGAR_PROOF_H

#include <map>
#include <set>
#include <sstream>
#include <string>

#include "../std_plugin.h"

namespace ethos {

class State;
class TypeChecker;
class Desugar;

/**
 */
class DesugarProof : public StdPlugin
{
 public:
  DesugarProof(State& s, Desugar* d);
  ~DesugarProof();
  void output(std::ostream& out);
  /** */
  void notifyAssume(const std::string& name,
                    Expr& proven,
                    bool isPush) override;
  /** */
  bool notifyStep(const std::string& name,
                  Expr& rule,
                  Expr& proven,
                  const std::vector<Expr>& premises,
                  const std::vector<Expr>& args,
                  bool isPop,
                  Expr& result,
                  std::ostream* err) override;
  /** bind */
  void bind(const std::string& name, const Expr& e) override;

 private:
  void printTerm(const Expr& e, std::ostream& os);
  Expr d_true;
  Expr d_boolType;
  // parent desugar
  Desugar* d_desugar;
  // the proof steps
  std::stringstream d_eoPfSteps;
  // NEW
  // timestamps of proof steps
  size_t getTimestampIndex(const Expr& e);
  std::map<Expr, size_t> d_timestamp;
  size_t d_currTimestamp;
  std::vector<size_t> d_timestampScope;
  std::stringstream d_cmds;
};

}  // namespace ethos

#endif /* DESUGAR_H */
