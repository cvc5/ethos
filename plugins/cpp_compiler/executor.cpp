/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "executor.h"

#include <iomanip>
#include <ostream>

namespace ethos {

Executor::Executor(State& state) : d_state(state) {}

Executor::~Executor() {}

void Executor::printConfig(std::ostream& out) const
{
  out << std::setw(15) << "signatures : " << std::endl;
  out << showCompiledFiles();
}

}  // namespace ethos
