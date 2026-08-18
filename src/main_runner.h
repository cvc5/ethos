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

/**
 * Constructs the plugin requested by the given options, if any. Used by
 * runMain to instantiate the plugin selected on the command line; returns
 * nullptr if no plugin was requested.
 */
using PluginFactory = std::unique_ptr<Plugin> (*)(Options&, State&);

/** Return true if the options request running a plugin. */
bool hasPluginRequest(const Options& opts);
/**
 * The shared main entry point of the ethos and ethos-eoc binaries: parses
 * the command line into options, constructs a plugin via pluginFactory if
 * one was requested, and runs the interpreter on the given inputs.
 */
int runMain(int argc, char* argv[], PluginFactory pluginFactory);

}  // namespace ethos

#endif
