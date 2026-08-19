/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include <cstdlib>

#include "compiler.h"
#include "state.h"

using namespace ethos;

int main(int argc, char** argv)
{
  if (argc != 2)
  {
    return 2;
  }
  Options options;
  Stats stats;
  State state(options, stats);
  Compiler compiler(state);
  state.setPlugin(&compiler);
  if (!state.includeFile(argv[1], true))
  {
    std::exit(3);
  }
  compiler.finalize();

  // State intentionally has process lifetime in the ethos executable. Match
  // that lifetime here instead of running its members' destructors in an
  // order they were not designed to support.
  std::exit(0);
}
