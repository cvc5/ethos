/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "executor.h"

namespace ethos {

std::string Executor::showCompiledFiles() { return ""; }

bool Executor::includeFile(const Filepath& path,
                           bool isSignature,
                           bool isReference,
                           const Expr& referenceNf)
{
  (void)path;
  (void)isSignature;
  (void)isReference;
  (void)referenceNf;
  return false;
}

void Executor::initialize() {}

}  // namespace ethos
