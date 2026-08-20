/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "plugin.h"

#if defined(ETHOS_PLUGIN_HEADER) != defined(ETHOS_PLUGIN_CLASS)
#error "ETHOS_PLUGIN_HEADER and ETHOS_PLUGIN_CLASS must be defined together"
#endif

#ifdef ETHOS_PLUGIN_HEADER
#include ETHOS_PLUGIN_HEADER
#endif

namespace ethos {

std::unique_ptr<Plugin> createPlugin(State& state)
{
#ifdef ETHOS_PLUGIN_CLASS
  return std::make_unique<ETHOS_PLUGIN_CLASS>(state);
#else
  (void)state;
  return nullptr;
#endif
}

}  // namespace ethos
