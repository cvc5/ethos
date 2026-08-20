/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef EXECUTOR_H
#define EXECUTOR_H

#include <string>

#include "plugin.h"

namespace ethos {

/** Plugin which loads signatures reconstructed by generated C++ code. */
class Executor : public Plugin
{
 public:
  explicit Executor(State& s);
  ~Executor() override;

  /** List the signature files embedded in the generated source. */
  static std::string showCompiledFiles();
  /** Return true when generated code already reconstructed this signature. */
  bool includeFile(const Filepath& path,
                   bool isSignature,
                   bool isReference,
                   const Expr& referenceNf) override;
  /** Append embedded signature paths to the build configuration. */
  void printConfig(std::ostream& out) const override;
  /** Reconstruct the embedded signatures in the associated State. */
  void initialize() override;

 private:
  State& d_state;
};

}  // namespace ethos

#endif /* EXECUTOR_H */
