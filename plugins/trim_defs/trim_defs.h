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
#include "state.h"

namespace ethos {

/**
 */
class TrimDefs : public Plugin
{
 public:
  TrimDefs(State& s);
  ~TrimDefs();
  /**
   * Include file, if not already done so.
   */
  void finalizeIncludeFile(const Filepath& s,
                           bool isSignature,
                           bool isReference,
                           const Expr& referenceNf) override;

                               /**
                                */
                              bool echo(const std::string& msg) override;
  /** Finalize */
  void finalize() override;
 private:
  /** the state */
  State& d_state;
  std::string d_defTarget;
  bool d_setDefTarget;
  size_t d_idCounter = 0;
  std::map<std::string, size_t> d_symToId;
  std::vector<std::string> d_commands;
  std::map<size_t, std::unordered_set<size_t>> d_symCommands;
  std::map<size_t, std::unordered_set<size_t>> d_cmdSyms;
  std::vector<size_t> d_toVisit;
  void parseCommands(std::istream& in);
};

}  // namespace ethos

#endif /* TRIM_DEFS_H */
