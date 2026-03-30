/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef ETHOS_MAIN_RUNNER_H
#define ETHOS_MAIN_RUNNER_H

#include <memory>

#include "plugin.h"
#include "state.h"

namespace ethos {

using PluginFactory = std::unique_ptr<Plugin> (*)(Options&, State&);

bool hasPluginRequest(const Options& opts);
int runMain(int argc, char* argv[], PluginFactory pluginFactory);

}  // namespace ethos

#endif
