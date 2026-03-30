/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/

#include "../plugins/desugar/desugar.h"
#include "../plugins/lean_meta/lean_meta_reduce.h"
#include "../plugins/model_smt/model_smt.h"
#include "../plugins/smt_meta/smt_meta_reduce.h"
#include "../plugins/trim_defs/trim_defs.h"
#include "main_runner.h"

namespace {

std::unique_ptr<ethos::Plugin> createPlugin(ethos::Options& opts,
                                            ethos::State& s)
{
  if (opts.d_pluginDesugar)
  {
    return std::unique_ptr<ethos::Plugin>(new ethos::Desugar(s));
  }
  if (opts.d_pluginSmtMeta)
  {
    return std::unique_ptr<ethos::Plugin>(new ethos::SmtMetaReduce(s));
  }
  if (opts.d_pluginLeanMeta)
  {
    return std::unique_ptr<ethos::Plugin>(new ethos::LeanMetaReduce(s));
  }
  if (opts.d_pluginTrimDefs)
  {
    return std::unique_ptr<ethos::Plugin>(new ethos::TrimDefs(s));
  }
  if (opts.d_pluginModelSmt)
  {
    return std::unique_ptr<ethos::Plugin>(new ethos::ModelSmt(s));
  }
  return nullptr;
}

}  // namespace

int main(int argc, char* argv[]) { return ethos::runMain(argc, argv, createPlugin); }
