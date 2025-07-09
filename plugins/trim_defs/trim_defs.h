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
#include <string>

#include "../std_plugin.h"
namespace ethos {

/**
 */
class TrimDefs : public StdPlugin
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
  std::vector<std::string> d_defTargets;
  size_t d_idCounter;
  std::map<std::string, size_t> d_symToId;
  std::vector<std::string> d_commands;
  std::map<size_t, std::unordered_set<size_t>> d_symCommands;
  std::map<size_t, std::unordered_set<size_t>> d_cmdSyms;
  std::vector<size_t> d_toVisit;
  void parseCommands(std::istream& in);
};

}  // namespace ethos

#endif /* TRIM_DEFS_H */
