/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "base/check.h"
#include "main_runner.h"

using namespace ethos;

namespace {

std::unique_ptr<Plugin> createPlugin(Options& opts, State&)
{
  if (hasPluginRequest(opts))
  {
    EO_FATAL() << "Error: plugin options are only available in ethos-eoc";
  }
  return nullptr;
}

}  // namespace

int main(int argc, char* argv[]) { return runMain(argc, argv, createPlugin); }
