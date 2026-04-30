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
 * Parsed top-level command from an EO file used by the trimming pass.
 */
struct Command
{
  /** Top-level command name, such as `program` or `declare-consts`. */
  std::string d_cmdName;
  /** Primary symbol introduced by the command. */
  std::string d_symbolName;
  /** Symbols referenced by the command body. */
  std::unordered_set<std::string> d_bodySyms;
  /** Original command text, preserved for output. */
  std::string d_fullText;
};

/**
 * Plugin that slices generated EO files down to the definitions needed by a
 * requested target symbol.
 *
 * `TrimDefs` reads signature files as raw top-level S-expressions, builds a
 * dependency graph from commands to the symbols they reference, and preserves
 * only commands reachable from one or more `(echo "trim-defs <symbol>")`
 * targets.  This is primarily used after desugaring and model_smt generation,
 * where the full generated signature can be much larger than a single VC or
 * proof-rule workflow needs.
 *
 * The pass is deliberately text-preserving: it keeps the original command
 * bodies and prints reachable commands back out in dependency order instead of
 * rebuilding them from typed expressions.
 */
class TrimDefs : public StdPlugin
{
 public:
  /** Construct the trimming plugin. */
  TrimDefs(State& s);
  /** Destroy the trimming plugin. */
  ~TrimDefs();
  /**
   * Read signature include files and index their top-level commands.
   */
  void finalizeIncludeFile(const Filepath& s,
                           bool isSignature,
                           bool isReference,
                           const Expr& referenceNf) override;

  /** Interpret trim-defs echo commands and suppress them from normal output. */
  bool echo(const std::string& msg) override;
  /** Compute the reachable command slice and emit the trimmed EO text. */
  void finalize() override;

 private:
  /** Add a parsed command to the dependency graph. */
  void processCommand(Command& cmd);
  /** Target symbols requested by trim-defs echo commands. */
  std::vector<std::string> d_defTargets;
  /** Next numeric id to assign to a symbol. */
  size_t d_idCounter;
  /** Map from symbol name to dependency-graph id. */
  std::map<std::string, size_t> d_symToId;
  /** Original command text indexed by command id. */
  std::vector<std::string> d_commands;
  /** Commands that introduce each symbol id. */
  std::map<size_t, std::unordered_set<size_t>> d_symCommands;
  /** Symbol ids referenced by each command id. */
  std::map<size_t, std::unordered_set<size_t>> d_cmdSyms;
  /** Worklist of symbol ids whose defining commands should be retained. */
  std::vector<size_t> d_toVisit;
  /** Parse all top-level commands from an input stream. */
  void parseCommands(std::istream& in);
};

}  // namespace ethos

#endif /* TRIM_DEFS_H */
